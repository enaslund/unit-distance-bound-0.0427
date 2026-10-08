"""Score quartic fields (2 split completely) with the fieldopt model.
Input lines: G r2 disc poly 3:[[e,f],..] 5:... ; output ranked deltas."""
import _paths  # noqa: F401
import sys, re, ast, numpy as np, time
from fieldopt import solve, compress
def parse(line):
    toks = line.split()
    G, r2, disc = toks[0], int(toks[1]), int(toks[2])
    rest = line.split(None, 3)[3]
    m = re.match(r'(.*?) (3:\[.*)', rest)
    poly = m.group(1); pdata = m.group(2)
    split = {2: [(1, 1)]*4}
    for item in re.findall(r'(\d+):(\[\[.*?\]\])', pdata):
        p = int(item[0]); lst = ast.literal_eval(item[1])
        split[p] = [tuple(x) for x in lst]
    return dict(G=G, r2=r2, disc=disc, poly=poly, split=split)
def field(rec, maxp=47):
    sp = {p: v for p, v in rec['split'].items() if p <= maxp}
    m = 4
    return dict(m=m, r1=m - 2*rec['r2'], r2=rec['r2'], logrd=np.log(abs(rec['disc']))/m, split=sp)
def margin_at(fd, delta, ts=np.arange(0.14, 0.32, 0.02)):
    best = (-np.inf, None)
    for t in ts:
        M, ch = solve(delta, t, fd)
        if M > best[0]: best = (M, (round(t, 3), ch))
    return best
def bisect(fd, lo=0.03, hi=0.1, iters=12):
    info = None
    for _ in range(iters):
        mid = (lo + hi)/2
        M, bi = margin_at(fd, mid)
        if M > 0: lo, info = mid, bi
        else: hi = mid
    return lo, info
if __name__ == "__main__":
    recs = [parse(l) for l in open(sys.argv[1]) if l.strip()]
    print(len(recs), "fields", file=sys.stderr)
    scored = []
    t0 = time.time()
    for i, r in enumerate(recs):
        fd = field(r)
        M, _ = margin_at(fd, 0.05, ts=np.arange(0.16, 0.30, 0.03))
        scored.append((M, i))
    scored.sort(reverse=True)
    print("screen done", time.time() - t0, file=sys.stderr)
    for M, i in scored[:25]:
        r = recs[i]; fd = field(r)
        d, info = bisect(fd)
        sp = {p: r['split'][p] for p in (3, 5, 7, 11, 13)}
        print(f"delta {d:.4f} M05 {M:+.4f} {r['G']} r2={r['r2']} disc={r['disc']} rd={abs(r['disc'])**0.25:.1f} {sp} {info[0] if info else ''} {compress(info[1]) if info else ''}", flush=True)
