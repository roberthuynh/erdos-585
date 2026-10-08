#!/usr/bin/env python3
"""Run plain unpruned nauty generation with the fresh decider; save every receipt."""
import datetime, hashlib, json, os, pathlib, re, subprocess, sys, time
HERE=pathlib.Path(__file__).resolve().parent
NA=pathlib.Path(os.environ.get('FINITE_NAUTY_DIR','nauty2_9_3'))
LOG=HERE/'receipts'; DATA=HERE/'data'
LOG.mkdir(exist_ok=True); DATA.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def census(label,args):
    generator=HERE/'geng_plain'
    cmd1=['timeout','240',str(generator),*map(str,args)]
    all_graphs=DATA/(label+'.all.g6'); cycles=DATA/(label+'.cycles.tsv')
    tee_command=['timeout','240','tee',str(all_graphs)]
    cmd2=['timeout','240',str(HERE/'pair_decider'),'--cert',str(cycles)]
    free=DATA/(label+'.free.g6'); glog=LOG/(label+'.geng.log'); dlog=LOG/(label+'.decider.log')
    started=datetime.datetime.now().astimezone().isoformat(); before=time.monotonic()
    with glog.open('wb') as ge,dlog.open('wb') as de,free.open('wb') as out:
        gen=subprocess.Popen(cmd1,stdout=subprocess.PIPE,stderr=ge)
        tee=subprocess.Popen(tee_command,stdin=gen.stdout,stdout=subprocess.PIPE)
        gen.stdout.close()
        dec=subprocess.Popen(cmd2,stdin=tee.stdout,stdout=out,stderr=de)
        tee.stdout.close()
        dx=dec.wait();tx=tee.wait();gx=gen.wait()
    elapsed=time.monotonic()-before
    summary=re.search(r'complete seen=(\d+) pair=(\d+) free=(\d+) supports=(\d+) first_cycles=(\d+) cpu=([\d.]+)',dlog.read_text())
    generated=re.search(r'>Z\s+(\d+) graphs generated',glog.read_text())
    record={'label':label,'started':started,'wall_seconds':elapsed,'generator_command':cmd1,
            'tee_command':tee_command,'decider_command':cmd2,'generator_exit':gx,'tee_exit':tx,'decider_exit':dx,
            'generator_binary_sha256':sha(generator),'generator_source_sha256':sha(HERE/'vendor/geng.c'),
            'decider_source_sha256':sha(HERE/'pair_decider.c'),'decider_binary_sha256':sha(HERE/'pair_decider'),
            'generator_log_sha256':sha(glog),'decider_log_sha256':sha(dlog),
            'free_catalogue_sha256':sha(free),'free_catalogue_lines':sum(1 for _ in free.open('rb')),
            'all_graphs_sha256':sha(all_graphs),'all_graphs_lines':sum(1 for _ in all_graphs.open('rb')),
            'cycle_certificates_sha256':sha(cycles),'cycle_certificate_lines':sum(1 for _ in cycles.open('rb'))}
    if summary:
        record.update(dict(zip(['seen','with_pair','pair_free','eligible_supports','first_cycles','cpu_seconds'],
              [int(x) for x in summary.groups()[:5]]+[float(summary.group(6))])))
    if generated: record['generated']=int(generated.group(1))
    record['complete']=gx==tx==dx==0 and summary is not None and generated is not None and record['seen']==record['generated']==record['all_graphs_lines'] and record['pair_free']==record['free_catalogue_lines'] and record['with_pair']==record['cycle_certificate_lines']
    (LOG/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record),flush=True)
    if not record['complete']: raise SystemExit('incomplete census '+label)
    return record
if __name__=='__main__':
    phase=sys.argv[1]
    if phase=='controls':
        for n in range(5,9):
            r=census('control-n'+str(n),[n])
            expected={5:33,6:148,7:954,8:10512}[n]
            assert r['pair_free']==expected,(n,r,expected)
    elif phase=='pilot':
        for e in (26,27):census('pilot-n10-e'+str(e),['-d4',10,f'{e}:{e}','0/64'])
    elif phase=='parents':
        for e in (26,27):census('parent-n10-e'+str(e),['-d4',10,f'{e}:{e}'])
    elif phase=='baseline':census('baseline-n10-e28',[10,'28:28'])
    else:raise SystemExit('phase must be controls, pilot, parents, or baseline')
