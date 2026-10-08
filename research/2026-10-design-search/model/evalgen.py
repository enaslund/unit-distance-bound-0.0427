"""Score fields (any degree m, 2 split completely) from lines: G r2 disc poly p:[[e,f],..] ..."""
import _paths  # noqa: F401
import sys, re, ast, numpy as np, time
from fieldopt2 import margin_at, bisect
from fieldopt import compress
def parse(line):
    toks = line.split()
    G, r2, disc = toks[0], int(toks[1]), int(toks[2])
    pdata = line[line.index(' 3:['):]
    poly = line.split(None, 3)[3][:line.split(None, 3)[3].index(' 3:[')]
    split = {}
    for p, lst in re.findall(r'(\d+):(\[\[.*?\]\])', pdata):
        split[int(p)] = [tuple(x) for x in ast.literal_eval(lst)]
    m = sum(e*f for e, f in split[3])
    split[2] = [(1, 1)]*m
    return dict(G=G, r2=r2, disc=disc, poly=poly, m=m,
                fd=dict(m=m, r1=m-2*r2, r2=r2, logrd=np.log(abs(disc))/m, split={p: v for p, v in split.items() if p <= 47}))
if __name__ == "__main__":
    rdmax = float(sys.argv[2])
    recs = [parse(l) for l in open(sys.argv[1]) if l.strip()]
    recs = [r for r in recs if abs(r['disc'])**(1/r['m']) <= rdmax]
    print(len(recs), "fields with rd <=", rdmax, file=sys.stderr)
    t0 = time.time()
    scored = []
    for i, r in enumerate(recs):
        M, _ = margin_at(r['fd'], 0.042, ts=np.arange(0.20, 0.34, 0.04))
        scored.append((M, i))
    scored.sort(reverse=True)
    print("screen", round(time.time()-t0), "s", file=sys.stderr)
    for M, i in scored[:15]:
        r = recs[i]
        d, info = bisect(r['fd'], lo=0.03, hi=0.07)
        sp = {p: r['fd']['split'][p] for p in (3, 5, 7)}
        print(f"delta {d:.4f} M042 {M:+.4f} {r['G']} r2={r['r2']} disc={r['disc']} rd={abs(r['disc'])**(1/r['m']):.1f} {sp} {info[0] if info else ''} {compress(info[1]) if info else ''}", flush=True)
