import json, re, hashlib, concurrent.futures, subprocess, os, sys
from pathlib import Path
from importlib.machinery import SourceFileLoader
common=SourceFileLoader('common',str(Path(__file__).with_name('compact-check.py'))).load_module()
w,root,cache,scope=common.w,common.root,common.cache,common.scope
work=common.work;patch_dir=w/('output-'+scope);patch_dir.mkdir(exist_ok=True)
srcdir=work/'src';srcdir.mkdir(exist_ok=True)
env=common.env
def test(m):
 rel=common.relative(m); arc=cache/(m.replace('.','/')+'.olean')
 if not arc.is_file():return None
 use=dict(candidates);t=srcdir/(m.replace('.','/')+'.lean');t.parent.mkdir(parents=True,exist_ok=True)
 for run in range(1,9):
  old,new,_,edits=common.build_candidate(m,use)
  if not edits:return None
  decls={}
  for a,b,s,n,mode in edits:decls.setdefault(n,set()).add(mode)
  testsrc='import Archive\n'+new+'\n'; lines=testsrc.splitlines();owners={}
  for n,modes in decls.items():
   pattern=re.compile(r'^(?:@\[[^\]\n]+\] )?(?:(?:noncomputable|private|protected) )*(?:def|theorem|lemma|abbrev) '+re.escape(n)+r' :')
   for j,line in enumerate(lines):
    if pattern.match(line):
     owners[j+1]=n
     for k in range(j+1,len(lines)):
      if lines[k] and not lines[k][0].isspace():break
      owners[k+1]=n
     break
   else: raise ValueError('cannot locate '+n)
  # An archive check imports only Lean and reads the pinned module's binary directly.
  # Each source elaboration runs in a fresh process under the original module name.
  for n,modes in decls.items():
   lines.append('#compare_with_archive '+n+' '+json.dumps(str(arc))+' '+str(int('VALUE' in modes)))
   owners[len(lines)]=n
  t.write_text('\n'.join(lines)+'\n');log=work/(m.split('.')[-1]+'.log')
  with log.open('w') as out:rc=subprocess.run(['lean','-j2','--tstack=400000','-R',str(srcdir),*common.options,str(t)],env=env,stdout=out,stderr=subprocess.STDOUT).returncode
  if rc==0 and "declaration uses 'sorry'" not in log.read_text():
   f=patch_dir/rel;f.parent.mkdir(parents=True,exist_ok=True);f.write_text(new)
   print('ACCEPT',m,len(edits),old.count('\n')-new.count('\n'),flush=True)
   return {'path':rel,'sourceSHA256':hashlib.sha256(old.encode()).hexdigest(),'afterSHA256':hashlib.sha256(new.encode()).hexdigest(),'saved':old.count('\n')-new.count('\n'),'changes':[(n,k) for a,b,s,n,k in edits]}
  errs=[int(x) for x in re.findall(r'\.lean:(\d+):\d+: error',log.read_text())];drop={owners[i] for i in errs if i in owners}
  if not drop: return None
  use={k:v for k,v in use.items() if k[1] not in drop}
 return None
if __name__=='__main__':
 subprocess.run(['lean','-j2','-R',str(w),'-o',str(w/'Archive.olean'),str(w/'Archive.lean')],env=env,check=True)
 candidates=common.read_dumps()
 # Every proposed edit must pass the source build, the compiled type comparison
 # and, for definitions, the compiled value comparison.
 mods=[m for m in common.rows if any(('TYPE',r[0])in candidates for r in common.rows[m])]
 with concurrent.futures.ThreadPoolExecutor(3) as ex: results=[r for r in ex.map(test,mods) if r]
 (patch_dir/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
 print('Accepted',len(results),'modules and',sum(r['saved'] for r in results),'lines')
