import sys, re, collections
# summarize rv c2 output lines
def parse(line):
    d = {}
    for tok in line.split():
        if '=' in tok:
            k, v = tok.split('=', 1)
            d[k] = v
    return d
for fn in sys.argv[1:]:
    rows = [parse(l) for l in open(fn) if l.startswith('g')]
    c = collections.Counter()
    for r in rows:
        c['graphs'] += 1
        c['sparse'] += int(r['sparse'])
        c['zu_'+r['zu']] += 1
        c['nbad'] += int(r['nbad'])
        t = list(map(int, r['badW_types[g,a,b1a,b1b,b2,o]'].split(',')))
        for name, x in zip(['g','a','b1a','b1b','b2','o'], t): c['badW_'+name] += x
        c['onlygamma'] += int(r['onlygamma'])
        c['core'] += int(r['core'])
        c['core_'+r['zu']] += int(r['core'])
        c['allportsbad'] += int(r['allportsbad'])
        c['n2b>0'] += int(r['n2b']) > 0
        c['asplit20>0'] += int(r['asplit20']) > 0
        c['asplit02>0'] += int(r['asplit02']) > 0
        c['goodport'] += int(r['goodport'])
        c['napet>0'] += int(r['napet']) > 0
        c['maxdbadport_'+r['zu']] = max(c['maxdbadport_'+r['zu']], int(r['dbadport']))
        c['maxnbad'] = max(c['maxnbad'], int(r['nbad']))
        c['lat20'] += int(r['lat20']); c['lat02'] += int(r['lat02'])
    print(fn, dict(c))
