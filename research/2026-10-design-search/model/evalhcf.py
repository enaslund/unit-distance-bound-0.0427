import _paths  # noqa: F401
import sys, ast, re, numpy as np
from fieldopt2 import margin_at, bisect
from fieldopt import compress
recs = []
for line in open(sys.argv[1]):
    toks = line.split(None, 3)
    D, hw, H = int(toks[0]), int(toks[1]), int(toks[2])
    split = {}
    for p, lst in re.findall(r'(\d+):(\[\[.*?\]\])', toks[3]):
        out = []
        for (e, f, n) in ast.literal_eval(lst):
            out += [(e, f)]*n
        split[int(p)] = out
    m = 2*H
    split[2] = [(1, 1)]*m
    cm = (H != hw)   # narrow HCF strictly bigger than wide HCF -> totally complex
    fd = dict(m=m, r1=0 if cm else m, r2=m//2 if cm else 0, logrd=0.5*np.log(D), split=split, cm=cm)
    recs.append((D, hw, H, fd))
scored = []
for D, hw, H, fd in recs:
    M, _ = margin_at(fd, 0.045, ts=np.arange(0.16, 0.34, 0.03))
    scored.append((M, D, hw, H, fd))
scored.sort(key=lambda r: -r[0])
for M, D, hw, H, fd in scored[:20]:
    d, info = bisect(fd)
    sp = {p: fd['split'][p][:3] for p in (3, 5, 7)}
    print(f"D {D} rd {D**0.5:.1f} h {hw} h+ {H} cm {fd['cm']} M045 {M:+.4f} delta {d:.4f} t {info[0] if info else ''} {sp} {compress(info[1]) if info else ''}", flush=True)
