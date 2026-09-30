# Fresh analytic replay of the manuscript certificate (September 22)

This directory records a fresh run, on 2026-09-22, of the manuscript's
analytic replay driver `certificates/reproduce.py --analytic`. It is a
record of that run and of its scope. It is not a Lean proof of the zeta
hypothesis (H) left open by `SolutionZeta.lean`, it does not change the
conditional status of the selected theorem, and it is not human-refereed.
The mathematical identification of the manuscript's ceiling with the
fixed-field quantity in (H) is described in
[external-zeta-20260921/README.md](../external-zeta-20260921/README.md);
this note adds only the fresh execution record.

## Command

The driver was run from the manuscript directory of the research
repository (`publication/unit-distance-1.0418235`, the manuscript shipped
under `docs/manuscript/` in the exported package without its
`certificates/` and `evidence/` data). Below, `<scratch>` is a temporary
directory outside the repository and `<venv>` is a Python 3.13.5 virtual
environment holding the manuscript's `requirements.txt` (mpmath 1.3.0,
python-flint 0.9.0, numpy). Standard output and error were captured to the
log file listed at the end.

```sh
cd <research-repository>/publication/unit-distance-1.0418235
TMPDIR=<scratch>/tmp-analytic <venv>/bin/python certificates/reproduce.py \
  --analytic --output <scratch>/unit-distance-analytic.json
```

The driver verifies and joins the three sealed data-archive parts in a
private temporary copy under `TMPDIR`, replays from that copy, and leaves
the repository unchanged.

## Host

8-CPU x86_64 Linux (Debian, kernel 6.12), Python 3.13.5, mpmath 1.3.0,
python-flint 0.9.0, PARI/GP 2.17.2. GMP development headers (`gmp.h`) are
absent on this host; only the runtime library is installed. The
`--moments` mode, which recompiles the moment producers and needs a C++17
compiler with GMP headers, could therefore not be run.

## Result

Wall time 252.6 s (`seconds` = 252.566; the analytic stage alone,
`analytic_replay.seconds`, 233.2 s). The top-level status is

```text
PASS consolidated certificate replay
```

with the driver's own scope flags, copied from the JSON record:

| Field | Value |
| --- | --- |
| `all_analytic_factors_reevaluated` | `true` |
| `complete_prime_sieve_regenerated` | `false` |
| `newest_64_moment_files_regenerated` | `false` |
| `all_earlier_moment_and_actual_field_data_regenerated` | `false` |

So every Hecke-factor bound was re-evaluated from the stored moment tables,
the independent census prefix was rechecked, the finite prime correction
was recertified and the Euler ceiling was reassembled. The moment tables
and the prime census through `10^12` were hash-checked as supplied finite
data, not regenerated. The log contains 189 `PASS` lines and no failure;
its final line is `PASS 1.0418235; fresh margin: [...]`.

### Fresh ceiling enclosure

The record stores the fresh ceiling as a ball with exact dyadic endpoints
under `analytic_replay.fresh_C` (`value = mantissa * 2^exponent`, both
exponents `-257`). Decoded to twenty significant digits:

```text
lower  0.042161773115604722708
upper  0.042161818939484246940
```

The driver's display of the same ball is `[0.0421618 +/- 2.69e-8]`. The
upper endpoint is below the manuscript's threshold `0.042161819` and below
the ceiling `0.042165819` used by the selected Lean theorem. The exact
rational sum of the five printed allowances,
`0.04216181893948094953138458` (see the September 21 note), lies inside
this enclosure. The width of the ball is about `4.6e-8`; it is an
enclosure of the certificate's ceiling, not a measurement of the true
left-hand side of (H).

### The embedded `exponent` field

The nested `analytic_replay` block carries its own `"exponent":
"1.0418123"`. That driver bundles the pre-retuning geometry witness, so its
embedded exponent is the older figure. The consolidated top-level
`"exponent"` is `"1.0418235"`, which is what the log's final `PASS` line
reports; the `1.0418123` value is not a claim about this package.

## Trust

This is a conventional computer-assisted proof argument: it depends on the
mathematical identification of actual fields and Hecke characters, the
proved analytic tails, exact finite algorithms, and their software
execution. The interval calculations use rigorous ball arithmetic as
described by [FLINT](https://flintlib.org/doc/arb.html). The meaning of
the successful maximal-order checks is documented by
[PARI's nfcertify reference](https://pari.math.u-bordeaux.fr/dochtml/html/General_number_fields.html#nfcertify).
Neither software documentation nor a hash comparison proves the
repository's mathematical identifications or the correctness of its
entire implementation.

The driver and the certificate code are AI-written and were reviewed by AI
agents; independent human review and a Lean proof of the full numerical
inequality remain separate work. The conditional submission does not
incorporate this external computation as a proved Lean lemma or a custom
axiom. This run was executed and recorded on 2026-09-22 by Claude Fable 5.1
(Anthropic) through Claude Code, under Eric Naslund's direction; it changed
no Lean proof text.

## Files

| File | Bytes | SHA-256 |
| --- | --- | --- |
| `analytic-replay-20260922.json` | 139452 | `34cad37d9e1fe935549db45b918a66e462f4c18655a84b024ebfc68c22682a9e` |
| `analytic-replay-20260922.log` | 18470 | `a8595cbfcb4cc16f0d83bc09555585870fa2a4c179c89eb49db3a8b5b807c657` |

The JSON file is the driver's `--output` record; the log is the captured
console output of the same run.
