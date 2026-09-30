# Independent exceptional Euler allowance

`exceptional_euler_log_check.py` reads the seven terms of the manuscript's
displayed `B_D(σ)` formula (`an:bad-restored`) at `σ = 12001/12000` and bounds
them using exact rational arithmetic. The seven prime/exponent/denominator
triples are `(2,4,32)`, `(3,2,4)`, `(5,2,4)`, `(7,4,8)`, `(11,4,8)`,
`(13,4,8)` and `(17,4,4)`. It checks the corresponding TeX strings and pins
the source hash.

For `p^{-fσ}=p^{-f}exp(-f log(p)/12000)`, it obtains a lower bound on
`log(p)` from 35 terms of the positive `atanh` series after decomposing
`p=2^k m`, `1≤m<2`. The even degree-eight Taylor polynomial then bounds the
exponential from above. Finally, 25 positive terms and a geometric tail
bound `-log(1-x)` from above. Every factor is rounded upward on a rational
grid before summation.

The checker exited zero and gives

```text
B_D(σ) ≤ 0.0417270231508987854209556
       < 0.041727023150898786.
```

The exact strict slack is `1447611/2500000000000000000000000` (about
`5.790444×10^-19`). This independently checks the finite transcendental
allowance. The local residue degrees that select the seven factors are
mathematical inputs from the manuscript and the source audit, not proved by
this script. The remaining analytic factor bounds and the fixed-field zeta
hypothesis are untouched.
