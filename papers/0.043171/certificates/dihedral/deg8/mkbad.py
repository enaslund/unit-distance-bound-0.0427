"""deg8_bad.json: per degree-8 family (key 'O1_O2') the twists' w, Q and Euler denominator polynomials at 2, 3, 5"""
import json, sys
out = {}
for f in sys.argv[2:]:
    d = json.load(open(f))
    o1, o2 = d["pair"]
    out[f"{o1}_{o2}"] = {"pair": d["pair"], "dFL": d["dFL"], "PSMALL": d["PSMALL"],
                         "twists": [{"w": tw["w"], "Q": tw["Q"], "2": tw["small"]["2"], "3": tw["small"]["3"], "5": tw["small"]["5"]}
                                    for tw in d["twists"]]}
open(sys.argv[1], 'w').write(json.dumps(out, indent=1) + "\n")
print("deg8_bad written", {k: len(v["twists"]) for k, v in out.items()})
