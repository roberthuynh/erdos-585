#!/usr/bin/env python3
"""Build the fresh detector and an explicit unhooked plain nauty geng binary."""
import datetime,hashlib,json,os,pathlib,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
NA=pathlib.Path(os.environ.get('FINITE_NAUTY_DIR','nauty2_9_3'))
LOG=HERE/'receipts';LOG.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert sha(HERE/'vendor/geng.c')=='12bba376483782ae40b132e0b66f42cbbbf3acb6c2468f8c0e33ccdd505fc2d0'
objects=['gtoolsW.o','nautyW1.o','nautilW1.o','naugraphW1.o','schreierW.o','naurng.o']
commands={
    'plain-generator':['timeout','240','gcc','-O3','-march=native','-DMAXN=WORDSIZE','-DWORDSIZE=32','-I'+str(NA),'-o',str(HERE/'geng_plain'),str(HERE/'vendor/geng.c'),*[str(NA/f) for f in objects]],
    'decider':['timeout','240','gcc','-O3','-std=c11','-Wall','-Wextra','-Werror',str(HERE/'pair_decider.c'),'-o',str(HERE/'pair_decider')]
}
for label,command in commands.items():
    before=time.monotonic();result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (LOG/(label+'-build.log')).write_bytes(result.stdout)
    assert result.returncode==0,result.stdout
    files=[HERE/'vendor/geng.c',HERE/'geng_plain',HERE/'vendor/COPYRIGHT',*[NA/f for f in objects],*[NA/f for f in ['nauty.h','naututil.h','gtools.h']]] if label=='plain-generator' else [HERE/'pair_decider.c',HERE/'pair_decider']
    record={'timestamp':datetime.datetime.now().astimezone().isoformat(),'command':command,'exit':result.returncode,
            'wall_seconds':time.monotonic()-before,'files':[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in files]}
    if label=='plain-generator':record['flags_have_no_PRUNE_or_SUMMARY_hook']=True
    (LOG/(label+'-build.json')).write_text(json.dumps(record,indent=2)+'\n')
    print(label,'build complete',flush=True)
