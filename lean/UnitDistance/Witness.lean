module

public import UnitDistance.Target
public import UnitDistance.LocalShells
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option backward.privateInPublic true


/-!
# The exact published witness

Rational data transcribed from the sealed manuscript witness at research commit
`eec70fd25ebe045c5df1c98370d613eaa3719c0c`. Decimal/scientific strings were parsed
as exact fractions, never as machine floating-point values. These definitions
are mathematical quantities, not replay flags. Their numerical bounds are
separate explicit hypotheses in `Certificate.lean`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace UnitDistance.Witness

def s : ℝ := (22920117 : ℝ) / 20000000
def a : ℝ := (64316620879 : ℝ) / 5000000000000000
def p : ℝ := 2 / (1 + increment)
def aCompact : ℝ := 2 * p * increment
def ceiling : ℝ := 42161819 / 1000000000
def thetaMin : ℝ := 4095 / 8192
def epsilon : ℝ := 1 / 1000000000
def logRD : ℝ := (9 / 4 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * Real.log 15015

def bernsteinCoefficients : Fin 4 → Fin 4 → ℚ :=
  ![![(1 / 1 : ℚ), (24129438977 / 10000000000 : ℚ), (2772179921 / 1000000000 : ℚ), (66857798061 / 10000000000 : ℚ)], ![(24129438977 / 10000000000 : ℚ), (2408311493 / 625000000 : ℚ), (46371750119 / 10000000000 : ℚ), (81307168183 / 10000000000 : ℚ)], ![(2772179921 / 1000000000 : ℚ), (46371750119 / 10000000000 : ℚ), (13657239771 / 2500000000 : ℚ), (23878161897 / 2500000000 : ℚ)], ![(66857798061 / 10000000000 : ℚ), (81307168183 / 10000000000 : ℚ), (23878161897 / 2500000000 : ℚ), (13865943061 / 1000000000 : ℚ)]]

def bernstein3 (i : Fin 4) (t : ℝ) : ℝ :=
  (Nat.choose 3 i : ℝ) * t ^ (i : ℕ) * (1-t) ^ (3 - (i : ℕ))

def polynomial (t u : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (bernsteinCoefficients i j : ℝ) *
    bernstein3 i t * bernstein3 j u

def compactProfile (z : ℂ) : ℝ := Real.exp (-aCompact * ‖z‖^2 / p)

def pairProfile (z : ℂ × ℂ) : ℝ :=
  let t := (1 + a * ‖z.1‖^2)⁻¹
  let u := (1 + a * ‖z.2‖^2)⁻¹
  t ^ s * u ^ s * polynomial t u

def compactMass : ℝ := ∫ z : ℂ, compactProfile z ^ p

def compactOverlap : ℝ := ∫ z : ℂ, compactProfile z * compactProfile (z + 1)

def pairMass : ℝ := ∫ z : ℂ × ℂ, pairProfile z ^ p

def pairOverlap : ℝ :=
  ∫ u : ℝ, ∫ z : ℂ × ℂ, pairProfile z *
    pairProfile (z.1 + (Real.exp u : ℂ), z.2 + (Real.exp (-u) : ℂ))

def JCompact : ℝ := Real.log compactOverlap - (1+increment) * Real.log compactMass

def JPair : ℝ := Real.log pairOverlap - (1+increment) * Real.log pairMass

def primes : Fin 11 → ℕ := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
def ramification : Fin 11 → ℕ := ![8, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1]
def residueDegree : Fin 11 → ℕ := ![4, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4]
def periodPower : Fin 11 → ℕ := ![7, 9, 6, 2, 2, 1, 1, 1, 1, 1, 1]
def shellWeights : Fin 11 → Fin 6 → ℚ :=
  ![![(1 / 1 : ℚ), (26451551392391 / 500000000000000 : ℚ), (5789489600511 / 2500000000000000 : ℚ), (5062920920247 / 50000000000000000 : ℚ), (22453923355659 / 5000000000000000000 : ℚ), (4031918631437 / 20000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (98866787345973 / 1000000000000000 : ℚ), (81985230138641 / 10000000000000000 : ℚ), (33899259591601 / 50000000000000000 : ℚ), (7073691794287 / 125000000000000000 : ℚ), (11864130273063 / 2500000000000000000 : ℚ)], ![(1 / 1 : ℚ), (15694696101781 / 500000000000000 : ℚ), (20832887856541 / 25000000000000000 : ℚ), (22242307460119 / 1000000000000000000 : ℚ), (60504358878881 / 100000000000000000000 : ℚ), (16737711273851 / 1000000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (5475537228781 / 25000000000000000 : ℚ), (243051987821 / 6250000000000000000 : ℚ), (83349312286089 / 1000000000000000000000000000 : ℚ), (16239748423571 / 10000000000000000000000000000000 : ℚ), (31643053340993 / 1000000000000000000000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (882671775669 / 40000000000000000 : ℚ), (52893244151477 / 100000000000000000000000 : ℚ), (32351541879579 / 100000000000000000000000000000 : ℚ), (3093552057317 / 2500000000000000000000000000000000 : ℚ), (23665384530683 / 5000000000000000000000000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (19753217475271 / 1000000000000000000 : ℚ), (23912895762421 / 500000000000000000000000 : ℚ), (577465472857 / 5000000000000000000000000000 : ℚ), (27890532331439 / 100000000000000000000000000000000000 : ℚ), (67353099910173 / 100000000000000000000000000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (51855578363751 / 10000000000000000000 : ℚ), (932340817081 / 200000000000000000000000 : ℚ), (20953854169957 / 5000000000000000000000000000000 : ℚ), (9418530145547 / 2500000000000000000000000000000000000 : ℚ), (33868217038473 / 10000000000000000000000000000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (30150737786821 / 10000000000000000000 : ℚ), (8877724088281 / 5000000000000000000000000 : ℚ), (2613998524199 / 2500000000000000000000000000000 : ℚ), (30787117133133 / 50000000000000000000000000000000000000 : ℚ), (18130204982799 / 50000000000000000000000000000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (12033271761207 / 10000000000000000000 : ℚ), (317236260693 / 1000000000000000000000000 : ℚ), (41816908606879 / 500000000000000000000000000000000 : ℚ), (22048599887241 / 1000000000000000000000000000000000000000 : ℚ), (5812729505639 / 1000000000000000000000000000000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (40183950841977 / 100000000000000000000 : ℚ), (42255710985501 / 1000000000000000000000000000 : ℚ), (8886856929921 / 2000000000000000000000000000000000 : ℚ), (23362589414241 / 50000000000000000000000000000000000000000 : ℚ), (49134184420207 / 1000000000000000000000000000000000000000000000000 : ℚ)], ![(1 / 1 : ℚ), (3666436525301 / 12500000000000000000 : ℚ), (25364272697667 / 1000000000000000000000000000 : ℚ), (40395513941639 / 10000000000000000000000000000000000 : ℚ), (64334537606741 / 100000000000000000000000000000000000000000 : ℚ), (10246020721641 / 100000000000000000000000000000000000000000000000 : ℚ)]]

def residueCard (v : Fin 11) : ℝ := (primes v : ℝ) ^ residueDegree v

def finiteLp (v : Fin 11) : ℝ :=
  ∑ i : Fin 6, Local.shellMass (residueCard v) i * (shellWeights v i : ℝ) ^ p

def finiteSecond (v : Fin 11) : ℝ :=
  ∑ i : Fin 6, Local.shellMass (residueCard v) i * (shellWeights v i : ℝ) ^ 2

def finiteTransition (v : Fin 11) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6,
    (shellWeights v i : ℝ) * Local.shellD (residueCard v) i j * (shellWeights v j : ℝ)

def finiteLogFunctional (v : Fin 11) : ℝ :=
  -increment * periodPower v * Real.log (residueCard v) +
    Real.log (((periodPower v : ℝ)+1) * finiteSecond v ^ 2 +
      2 * finiteSecond v * finiteTransition v) -
    2 * (1+increment) * Real.log (finiteLp v)

def finiteProfit : ℝ :=
  ∑ v : Fin 11, finiteLogFunctional v / (ramification v * residueDegree v)

def margin (θ : ℝ) : ℝ :=
  finiteProfit - (1/2-increment)*logRD - ceiling + (1-increment)*Real.log 2 +
    (1-θ)*Real.log Real.pi + (1-2*θ)*JCompact + θ*JPair

theorem p_mul_exponent : p * (1+increment) = 2 := by
  unfold p
  field_simp [ne_of_gt (show 0 < 1+increment by linarith [increment_pos])]

theorem witness_basic : 0 < s ∧ 0 < a ∧ 0 < p ∧ 0 < epsilon ∧
    0 < thetaMin ∧ thetaMin < 1/2 := by
  norm_num [s, a, p, epsilon, thetaMin, increment]

theorem bernsteinCoefficients_pos (i j : Fin 4) : 0 < bernsteinCoefficients i j := by
  fin_cases i <;> fin_cases j <;> norm_num [bernsteinCoefficients]

theorem shellWeights_pos (v : Fin 11) (i : Fin 6) : 0 < shellWeights v i := by
  fin_cases v <;> fin_cases i <;> norm_num [shellWeights]

end UnitDistance.Witness
