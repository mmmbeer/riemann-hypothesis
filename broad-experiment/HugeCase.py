import json, subprocess, hashlib, gzip, os, sys, concurrent.futures, urllib.request, urllib.error, time
from pathlib import Path
root=Path.cwd(); w=root/'broad-experiment'; work=w/'tmp';work.mkdir(exist_ok=True)
mods=(w/'orig-mods-4000').read_text().splitlines()
url='https://rh-cache.taucetiproject.org/'
def get(url,path):
 for n in range(4):
  try:
   with urllib.request.urlopen(url,timeout=50) as a,path.open('wb') as b:
    while chunk:=a.read(65536):b.write(chunk)
   return
  except (OSError,urllib.error.URLError):
   if n==3:raise
   time.sleep(1+n)
mf=work/'modules.gz';get(url+'bootstrap/e50d09817ad81469f737e8f637561e6ccf86c670/modules.jsonl.gz',mf)
assert hashlib.sha256(mf.read_bytes()).hexdigest()==(w/'manifest-sha').read_text().strip()
with gzip.open(mf,'rt') as f:
 next(f);manifest={n:(h,a,d) for n,h,a,d in map(json.loads,f)}
def artifact(mod):
 h,a,d=manifest[mod]; pkg=work/(a[:16]+'.art'); p=work/(mod.replace('.','/')+'.olean');p.parent.mkdir(parents=True,exist_ok=True)
 get(url+'artifacts/leanprover-community/riemann-hypothesis/'+pkg.name,pkg)
 assert hashlib.sha256(pkg.read_bytes()).hexdigest()==d
 subprocess.run(['leantar','-x','-j','-'],input=json.dumps([{'file':str(pkg),'hash':h,'base':[str(p.parent),str(p.parent)]}]),text=True,check=True,stdout=subprocess.DEVNULL)
 pkg.unlink();assert p.exists()
mode=sys.argv[1]
if mode=='small':use=(w/'orig-mods-20').read_text().splitlines()
else:use=mods
with concurrent.futures.ThreadPoolExecutor(14) as ex:list(ex.map(artifact,use))
print('Verified',len(use),'project module archives',flush=True)
env=dict(os.environ,LEAN_PATH=str(w)+':'+str(work)+':'+os.environ['LEAN_PATH'],LEAN_ABORT_ON_PANIC='1')
def run(args): subprocess.run(['lean','-j2','-R',str(w),*map(str,args)],env=env,check=True)
run(['-o',w/'Env.olean',w/'Env.lean']);run(['-o',w/'Val.olean',w/'Val.lean'])
for name in (['Batch','Values'] if mode=='small' else ['Large']):
 with (w/(name+'.txt')).open('w') as out:
  res=subprocess.run(['lean','-j2','-R',str(w),str(w/(name+'.lean'))],env=env,stdout=out,stderr=subprocess.STDOUT)
 print(name,res.returncode,(w/(name+'.txt')).stat().st_size,flush=True)
