import os,re,subprocess
from pathlib import Path
w=Path('broad-experiment').resolve()
targets=sorted({m for nm in ['Batch','Values'] for m in re.findall(r'^import (\S+)',(w/(nm+'.lean')).read_text(),re.M) if m not in ['Env','Val']})
subprocess.run(['lake','build',*targets],check=True)
env=dict(os.environ,LEAN_PATH=str(w)+':'+os.environ['LEAN_PATH'],LEAN_ABORT_ON_PANIC='1')
for nm in ['Env','Val']:
 subprocess.run(['lean','-j2','-R',str(w),'-o',str(w/(nm+'.olean')),str(w/(nm+'.lean'))],env=env,check=True)
for nm in ['Batch','Values']:
 with (w/(nm+'.txt')).open('w') as out:
  subprocess.run(['lean','-j2','-R',str(w),str(w/(nm+'.lean'))],env=env,stdout=out,stderr=subprocess.STDOUT)
