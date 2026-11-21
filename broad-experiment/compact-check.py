"""Generate and validate smaller source descriptions of compiled declarations."""
import ast, bisect, concurrent.futures, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path

w=Path(__file__).resolve().parent
root=Path(os.environ.get('FORK_DIR',w.parent)).resolve()
scope=sys.argv[1]
cache=Path(os.environ.get('ARCHIVES',w/'tmp')).resolve()
work=w/('test-'+scope);work.mkdir(exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(w)+':'+str(cache)+':'+os.environ['LEAN_PATH'],LEAN_ABORT_ON_PANIC='1')
rows=json.loads((w/'types.json').read_text());values=json.loads((w/'terms.json').read_text())
schema={c['name']:c['binders'] for x in (w/'binders.jsonl').read_text().splitlines() if (c:=json.loads(x))}
from importlib.machinery import SourceFileLoader
def read_dumps():
 ops={};allowed=set()
 for file in (['Batch','Values'] if scope=='small' else ['Large']):
  for mode,n,expr in re.findall(r'^@@(TYPE|VALUE) ([^\n ]+)\n(.*?)\n@@END$',(w/(file+'.txt')).read_text(),re.M|re.S):
   if n=='goal1' or any(tok in expr for tok in ('⋯','✝','sorry','admit','unreachable!','_private.', '?m.', 'native_decide')):continue
   if n not in schema:continue
   ops[(mode,n)]=expr
 return ops
options=['-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-DmaxHeartbeats=4000000']
def runlean(args,log):
 with log.open('w') as out:return subprocess.run(['lean','-j2',*options,*map(str,args)],env=env,stdout=out,stderr=subprocess.STDOUT).returncode
def relative(m):return 'src/'+m.replace('.','/')+'.lean'
def extract(mode,n,x):
 return '#same_signature '+n+' matches (\n'+x+'\n)' if mode=='TYPE' else 'example : @'+n+' = (show (type_of% @'+n+') from\n'+x+'\n) := rfl'
def prep(ops):
 names={r[0]:m for m,rs in rows.items() for r in rs}
 mods=sorted({names[n] for mode,n in ops if n in names})
 lines=['import Env',*['import '+m for m in mods]]
 spans=[];order=[]
 for (mode,n),expr in ops.items():
  if n not in names:continue
  spans.append(len(lines)+1);order.append((mode,n));lines.extend(extract(mode,n,expr).splitlines())
 f=work/'Roundtrip.lean';f.write_text('\n'.join(lines)+'\n'); log=work/'roundtrip.log';code=runlean([f],log)
 err=set()
 for num in re.findall(r'Roundtrip.lean:(\d+):\d+: error',log.read_text()):
  j=bisect.bisect_right(spans,int(num))-1
  if j<0:raise Exception('import failure: '+log.read_text()[:2000])
  err.add(order[j])
 if code!=0 and not err:raise Exception('signature check: '+log.read_text()[-4000:])
 return {k:ops[k] for k in order if k not in err}
def build_candidate(m,ops):
 rel=relative(m);before=(root/rel).read_text()
 old=subprocess.check_output(['git','-C',str(root),'show','0f8a0bca44c2fe3301ba4738dd7f399f56bedac5:'+rel]).decode()
 edits=[];checks=[]
 for mode,arr in [('TYPE',rows[m]),('VALUE',values.get(m,[]))]:
  for n,a,b,*rest in arr:
   if (mode,n) not in ops:continue
   c,d=(a,b) if mode=='TYPE' else rest[:2];expr=ops[(mode,n)]
   src=old[c:d];replacement='\n'+'\n'.join('    '+line for line in expr.splitlines())
   if src.count('\n')-replacement.count('\n')<3 or len(replacement)>len(src):continue
   anchor=old.rfind(n+' :',0,a+1)
   if anchor<0:continue
   pref=old[anchor:d]
   if before.count(pref)!=1:continue
   pos=before.index(pref)+c-anchor
   edits.append((pos,pos+len(src),replacement,n,mode))
   checks.append(extract(mode,n,src))
 out=before
 for a,b,s,_,_ in sorted(edits,reverse=True):out=out[:a]+s+out[b:]
 return before,out,checks,edits
def main():
 ops=read_dumps();print('extracted',len(ops),flush=True); validity=prep(ops);print('roundtrip',len(validity),flush=True)
 docs={};files=[]
 for m in rows:
  old,new,checks,edits=build_candidate(m,validity)
  if not edits:continue
  direct=re.findall(r'^import (\S+)',new,re.M)
  if any((root/relative(dep)).exists() and not (cache/(dep.replace('.','/')+'.olean')).exists() for dep in direct):continue
  stem='M'+hashlib.sha256(m.encode()).hexdigest()[:12]
  tmp=work/(stem+'.lean');tmp.write_text('import Env\n'+new+'\n'+'\n'.join(checks)+'\n')
  files.append((m,str(tmp)));docs[m]=(old,new,edits)
 # Group by imports. Each module gets an independent elaboration environment.
 def imps(q):return tuple(re.findall('^import (.*)$',Path(q[1]).read_text(),re.M))
 files.sort(key=imps);listing=work/'files'; listing.write_text(''.join(m+'\t'+str(p)+'\n' for m,p in files))
 print('testing modules',len(files),flush=True)
 log=work/'source.log';code=runlean(['--run',w/'BatchCheck.lean',listing],log)
 for ln in log.read_text().splitlines():
  if ln.startswith('@@MODULE ') or 'error:' in ln:print(ln[:180])
 passed=re.findall(r'^@@MODULE (\S+) PASS$',log.read_text(),re.M)
 patch_dir=w/('output-'+scope);patch_dir.mkdir(exist_ok=True);record=[]
 for m in passed:
  before,out,edits=docs[m]; f=patch_dir/relative(m);f.parent.mkdir(parents=True,exist_ok=True);f.write_text(out)
  record.append({'path':relative(m),'sourceSHA256':hashlib.sha256(before.encode()).hexdigest(),'afterSHA256':hashlib.sha256(out.encode()).hexdigest(),'saved':before.count('\n')-out.count('\n'),'changes':[(n,k) for a,b,s,n,k in edits]})
 (patch_dir/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
 print('Accepted',len(passed), 'modules and', sum(x['saved'] for x in record),'lines',flush=True)
 if code or len(passed)!=len(files):print('Some candidate checks failed. See source.log.')
if __name__=='__main__':main()
