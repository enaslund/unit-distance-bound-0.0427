module

public import UnitDistance.Sqrt241.Target
public import UnitDistance.LocalShells
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option backward.privateInPublic true


/-!
# The witness for the tower over `ℚ(√241)` at δ = 0.04315

Port of `UnitDistance.Witness` with the five local types of
`certificates/finite-witness-241.json`: rational primes 2, 3, 5, 29 and 41 with
absolute (e, f) = (8,4), (2,2), (2,2), (1,4), (2,4). At 41 only the primes of the
tower above the capped prime of `ℚ(√241)` carry windows; they have true type (1,4) and
are half of the primes above 41, which the effective type (2,4) records. The pair
profile is the 1.0418235 manuscript's unchanged (`s`, `a` and the Bernstein matrix of
`UnitDistance.Witness`), so `pairProfile` and `pairOverlap` coincide with those of
the ℚ development and only the mass exponent changes: `q = s·p − 1`
(`pair_exponent_gap`). `ceiling` is the threshold for the fixed-base residue ceiling
of the tower fields; `thetaMin = 65535/131072` corresponds to a conjugacy class of
complex conjugation of size at least `2^15` in `Gal(K/B)`. These are definitions only;
their numerical bounds are proved separately (`Numerics/`, `FiniteCertificates/`).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace UnitDistance.Sqrt241.Witness

/-- The radial exponent `s` of the pair profile (the manuscript's value). -/
def s : ℝ := (22920117 : ℝ) / 20000000
/-- The radial scale `a` of the pair profile (the manuscript's value). -/
def a : ℝ := (64316620879 : ℝ) / 5000000000000000
/-- The mass exponent `p = 2/(1+δ)`, `δ = increment`. -/
def p : ℝ := 2 / (1 + increment)
/-- The Gaussian parameter `2pδ` of the compact-place profile. -/
def aCompact : ℝ := 2 * p * increment
/-- The threshold `0.0425` for the fixed-base residue ceiling of the tower fields. -/
def ceiling : ℝ := 425 / 10000
/-- The lower bound `(1 - 2⁻¹⁶)/2` for the complex-place proportion `θ` of the fixed
field of a complex conjugation with centralizer index at least `2^16`. -/
def thetaMin : ℝ := 65535 / 131072
/-- The concentration parameter `ε = 10⁻⁹` (the margin is used after a loss `4ε`). -/
def epsilon : ℝ := 1 / 1000000000
/-- `ℓ = (9/4) log 2 + (1/2) log 3615`, the bound for the logarithmic root discriminant of
the tower fields (the same body as `logRD` of `ChallengeZeta241.lean`). -/
def logRD : ℝ := (9 / 4 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * Real.log 3615

/-- The manuscript's Bernstein matrix, unchanged. -/
def bernsteinCoefficients : Fin 4 → Fin 4 → ℚ :=
  ![![(1 / 1 : ℚ), (24129438977 / 10000000000 : ℚ), (2772179921 / 1000000000 : ℚ), (66857798061 / 10000000000 : ℚ)], ![(24129438977 / 10000000000 : ℚ), (2408311493 / 625000000 : ℚ), (46371750119 / 10000000000 : ℚ), (81307168183 / 10000000000 : ℚ)], ![(2772179921 / 1000000000 : ℚ), (46371750119 / 10000000000 : ℚ), (13657239771 / 2500000000 : ℚ), (23878161897 / 2500000000 : ℚ)], ![(66857798061 / 10000000000 : ℚ), (81307168183 / 10000000000 : ℚ), (23878161897 / 2500000000 : ℚ), (13865943061 / 1000000000 : ℚ)]]

/-- The cubic Bernstein basis polynomial `C(3,i) tⁱ (1-t)^(3-i)`. -/
def bernstein3 (i : Fin 4) (t : ℝ) : ℝ :=
  (Nat.choose 3 i : ℝ) * t ^ (i : ℕ) * (1-t) ^ (3 - (i : ℕ))

/-- The Bernstein polynomial `P(t,u) = Σ c_ij B_i(t) B_j(u)` of the pair profile. -/
def polynomial (t u : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (bernsteinCoefficients i j : ℝ) *
    bernstein3 i t * bernstein3 j u

/-- The Gaussian profile `exp(-aCompact ‖z‖²/p)` at the compact places. -/
def compactProfile (z : ℂ) : ℝ := Real.exp (-aCompact * ‖z‖^2 / p)

/-- The pair profile `t^s u^s P(t,u)` with `t = (1 + a‖z₁‖²)⁻¹`, `u = (1 + a‖z₂‖²)⁻¹`. -/
def pairProfile (z : ℂ × ℂ) : ℝ :=
  let t := (1 + a * ‖z.1‖^2)⁻¹
  let u := (1 + a * ‖z.2‖^2)⁻¹
  t ^ s * u ^ s * polynomial t u

/-- The `L^p` mass `∫ compactProfile^p` of the compact-place profile. -/
def compactMass : ℝ := ∫ z : ℂ, compactProfile z ^ p

/-- The overlap `∫ compactProfile(z) compactProfile(z+1)` of the compact-place profile. -/
def compactOverlap : ℝ := ∫ z : ℂ, compactProfile z * compactProfile (z + 1)

/-- The `L^p` mass `∫ pairProfile^p` of the pair profile over `ℂ × ℂ`. -/
def pairMass : ℝ := ∫ z : ℂ × ℂ, pairProfile z ^ p

/-- The overlap of the pair profile with its shifts by `(eᵘ, e⁻ᵘ)`, integrated over `u ∈ ℝ`. -/
def pairOverlap : ℝ :=
  ∫ u : ℝ, ∫ z : ℂ × ℂ, pairProfile z *
    pairProfile (z.1 + (Real.exp u : ℂ), z.2 + (Real.exp (-u) : ℂ))

/-- The compact-place functional `log compactOverlap - (1+δ) log compactMass`. -/
def JCompact : ℝ := Real.log compactOverlap - (1+increment) * Real.log compactMass

/-- The pair functional `log pairOverlap - (1+δ) log pairMass`. -/
def JPair : ℝ := Real.log pairOverlap - (1+increment) * Real.log pairMass

/-- The five witness primes. -/
def primes : Fin 5 → ℕ := ![2, 3, 5, 29, 41]
/-- The absolute ramification indices `e` at the witness primes. -/
def ramification : Fin 5 → ℕ := ![8, 2, 2, 1, 2]
/-- The absolute residue degrees `f` at the witness primes. -/
def residueDegree : Fin 5 → ℕ := ![4, 2, 2, 4, 4]
/-- The period exponents `k` of the finite-place shell functions (`period` in
`certificates/finite-witness-241.json`). -/
def periodPower : Fin 5 → ℕ := ![7, 9, 6, 1, 1]
/-- The six shell weights at each witness prime (`weights` in
`certificates/finite-witness-241.json`). -/
def shellWeights : Fin 5 → Fin 6 → ℚ :=
  ![![(1 / 1 : ℚ), (4509124288194 / 96956058240835 : ℚ), (30486659864 / 15431412416677 : ℚ), (4750817593 / 55833807291627 : ℚ), (312557292 / 83683070090213 : ℚ), (10202986 / 61336650248189 : ℚ)], ![(1 / 1 : ℚ), (3557293422470 / 41587294680821 : ℚ), (4473097537 / 648982313134 : ℚ), (26849579809 / 47776963967923 : ℚ), (2513662972 / 54092619562375 : ℚ), (282581518 / 72995375851841 : ℚ)], ![(1 / 1 : ℚ), (1193123103534 / 42681663198781 : ℚ), (47239103179 / 65579497149591 : ℚ), (123442883 / 6520756159540 : ℚ), (23800649 / 46724632351127 : ℚ), (581851 / 41663755329659 : ℚ)], ![(1 / 1 : ℚ), (8517707 / 22940059243274 : ℚ), (13 / 99293481491072 : ℚ), (13 / 99293481491072000000 : ℚ), (13 / 99293481491072000000000000 : ℚ), (13 / 99293481491072000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (6670914 / 90087681134399 : ℚ), (1 / 100000000000000 : ℚ), (1 / 100000000000000000000 : ℚ), (1 / 100000000000000000000000000 : ℚ), (1 / 100000000000000000000000000000000 : ℚ)]]

/-- The residue field size `q = p^f` at the witness prime `v`. -/
def residueCard (v : Fin 5) : ℝ := (primes v : ℝ) ^ residueDegree v

/-- The `L^p` mass `Σᵢ shellMassᵢ · wᵢ^p` of the shell function at `v`. -/
def finiteLp (v : Fin 5) : ℝ :=
  ∑ i : Fin 6, Local.shellMass (residueCard v) i * (shellWeights v i : ℝ) ^ p

/-- The `L²` mass `Σᵢ shellMassᵢ · wᵢ²` of the shell function at `v`. -/
def finiteSecond (v : Fin 5) : ℝ :=
  ∑ i : Fin 6, Local.shellMass (residueCard v) i * (shellWeights v i : ℝ) ^ 2

/-- The transition form `Σᵢⱼ wᵢ Dᵢⱼ wⱼ` of the shell function at `v`. -/
def finiteTransition (v : Fin 5) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6,
    (shellWeights v i : ℝ) * Local.shellD (residueCard v) i j * (shellWeights v j : ℝ)

/-- The local functional at `v`: `-δ k log q + log((k+1) S² + 2 S T) - 2(1+δ) log Lₚ`
with `S = finiteSecond v`, `T = finiteTransition v`, `Lₚ = finiteLp v`. -/
def finiteLogFunctional (v : Fin 5) : ℝ :=
  -increment * periodPower v * Real.log (residueCard v) +
    Real.log (((periodPower v : ℝ)+1) * finiteSecond v ^ 2 +
      2 * finiteSecond v * finiteTransition v) -
    2 * (1+increment) * Real.log (finiteLp v)

/-- The finite-place profit `Σ_v finiteLogFunctional v / (e_v f_v)`. -/
def finiteProfit : ℝ :=
  ∑ v : Fin 5, finiteLogFunctional v / (ramification v * residueDegree v)

/-- The margin of the construction at complex-place proportion `θ`. -/
def margin (θ : ℝ) : ℝ :=
  finiteProfit - (1/2-increment)*logRD - ceiling + (1-increment)*Real.log 2 +
    (1-θ)*Real.log Real.pi + (1-2*θ)*JCompact + θ*JPair

/-- `p (1 + δ) = 2`. -/
theorem p_mul_exponent : p * (1+increment) = 2 := by
  unfold p
  field_simp [ne_of_gt (show 0 < 1+increment by linarith [increment_pos])]

/-- The beta exponent `q = s p - 1` of the pair mass. -/
theorem pair_exponent_gap : s * p - 1 = 12488617 / 10431500 := by
  norm_num [s, p, increment]

/-- Positivity of the profile parameters and `0 < thetaMin < 1/2`. -/
theorem witness_basic : 0 < s ∧ 0 < a ∧ 0 < p ∧ 0 < epsilon ∧
    0 < thetaMin ∧ thetaMin < 1/2 := by
  norm_num [s, a, p, epsilon, thetaMin, increment]

/-- The Bernstein coefficients are positive. -/
theorem bernsteinCoefficients_pos (i j : Fin 4) : 0 < bernsteinCoefficients i j := by
  fin_cases i <;> fin_cases j <;> norm_num [bernsteinCoefficients]

/-- The shell weights are positive. -/
theorem shellWeights_pos (v : Fin 5) (i : Fin 6) : 0 < shellWeights v i := by
  fin_cases v <;> fin_cases i <;> norm_num [shellWeights]

end UnitDistance.Sqrt241.Witness
