#!/usr/bin/env python3
"""Resume disjoint nauty residue classes for the 12-vertex, 36-edge audit.

The minimum degree five follows from the independently exhausted f(11)=31:
deleting a vertex of degree at most four would leave at least 32 edges.
Nauty's res/mod classes cover its canonical search without overlap. Only
successfully completed classes count. This is one computational method.
"""
import json
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'reports/585-overnight'


def run():
    started = time.monotonic()
    state = dict(modulus=32, completed=[], incomplete=[], outputs=0,
                 status='incomplete', minimum_degree_justification='f(11)=31 computational audit')
    for residue in range(32):
        stem = OUT/f'geng-twelve-36-part{residue:02d}'
        log = stem.with_suffix('.log')
        txt = log.read_text() if log.exists() else ''
        match = re.search(r'>Z (\d+) graphs generated', txt)
        if match is None and time.monotonic()-started < 165:
            with log.open('w') as err, stem.with_suffix('.stdout').open('w') as out:
                result = subprocess.run(['timeout','210','[temporary path]','-d5',
                    '12','36:36',f'{residue}/32',str(stem.with_suffix('.g6'))],
                    stdout=out,stderr=err)
            txt = log.read_text()
            match = re.search(r'>Z (\d+) graphs generated', txt) if result.returncode==0 else None
        if match:
            state['completed'].append(residue)
            state['outputs'] += int(match.group(1))
        else:
            state['incomplete'].append(residue)
        print(residue, 'complete' if match else 'pending', flush=True)
        state['status'] = 'complete' if len(state['completed'])==32 else 'incomplete'
        (OUT/'geng-twelve-partition-state.json').write_text(json.dumps(state,indent=2)+'\n')


if __name__ == '__main__':
    run()
