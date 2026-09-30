module

public import UnitDistance.PairOverlapLaplace
public import UnitDistance.Witness

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact finite data for the collected pair-overlap bound

The published overlap calculation first changes the degree-three Bernstein
polynomial to the power basis and then collects the hyperbola-series terms of
orders zero and one.  Every definition in this file is rational, so the four
large contractions can be checked by the kernel.
-/

noncomputable section

open scoped BigOperators

namespace UnitDistance.Witness

/-- The exact rational power-basis coefficients of `polynomial`. -/
def pairOverlapPowerCoefficient : Fin 4 → Fin 4 → ℚ :=
  ![![(1 : ℚ), 42388316931 / 10000000000, -3951404529 / 1250000000,
      23040358681 / 5000000000],
    ![42388316931 / 10000000000, 1233476703 / 5000000000,
      1117209393 / 312500000, -37257860547 / 10000000000],
    ![-3951404529 / 1250000000, 1117209393 / 312500000,
      -2193824061 / 312500000, 65331233457 / 10000000000],
    ![23040358681 / 5000000000, -37257860547 / 10000000000,
      65331233457 / 10000000000, -22484447969 / 5000000000]]

theorem polynomial_eq_pairOverlapPowerBasis (t u : ℝ) :
    polynomial t u =
      ∑ i : Fin 4, ∑ j : Fin 4,
        (pairOverlapPowerCoefficient i j : ℝ) * t ^ (i : ℕ) * u ^ (j : ℕ) := by
  norm_num [polynomial, bernstein3, bernsteinCoefficients,
    pairOverlapPowerCoefficient, Fin.sum_univ_succ, Nat.choose]
  ring

/-- Rational copies of the exponents used in the finite contraction. -/
def pairOverlapSQ : ℚ := 22920117 / 20000000
def pairOverlapEtaQ : ℚ := 2 * pairOverlapSQ - 1

def pairOverlapShiftSum (x : ℚ) (n : ℕ) : ℚ :=
  ∑ h ∈ Finset.range n, 1 / (x + h)

def pairOverlapK0 (i k : Fin 4) : ℚ :=
  1 / (pairOverlapEtaQ + (i : ℕ) + (k : ℕ))

def pairOverlapK1 (i k : Fin 4) : ℚ :=
  ((pairOverlapSQ + (i : ℕ)) * (pairOverlapSQ + (k : ℕ))) /
    ((pairOverlapEtaQ + (i : ℕ) + (k : ℕ) + 1) *
      (pairOverlapEtaQ + (i : ℕ) + (k : ℕ) + 2))

def pairOverlapR0 (i k : Fin 4) : ℚ :=
  pairOverlapK0 i k *
    (-1 / pairOverlapEtaQ
      - pairOverlapShiftSum pairOverlapEtaQ ((i : ℕ) + (k : ℕ)) / 2
      + pairOverlapShiftSum pairOverlapEtaQ ((i : ℕ) + (k : ℕ) + 1)
      - (pairOverlapShiftSum pairOverlapSQ (i : ℕ) +
          pairOverlapShiftSum pairOverlapSQ (k : ℕ)) / 2)

def pairOverlapR1 (i k : Fin 4) : ℚ :=
  pairOverlapK1 i k *
    (-1 / pairOverlapEtaQ + 1 / 2
      - pairOverlapShiftSum pairOverlapEtaQ ((i : ℕ) + (k : ℕ) + 1) / 2
      + pairOverlapShiftSum pairOverlapEtaQ ((i : ℕ) + (k : ℕ) + 3)
      - (pairOverlapShiftSum pairOverlapSQ ((i : ℕ) + 1) +
          pairOverlapShiftSum pairOverlapSQ ((k : ℕ) + 1)) / 2)

def pairOverlapB0 : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
    pairOverlapPowerCoefficient i j * pairOverlapPowerCoefficient k l *
      pairOverlapK0 i k * pairOverlapK0 j l

def pairOverlapB1 : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
    pairOverlapPowerCoefficient i j * pairOverlapPowerCoefficient k l *
      pairOverlapK1 i k * pairOverlapK1 j l

def pairOverlapV0 : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
    pairOverlapPowerCoefficient i j * pairOverlapPowerCoefficient k l *
      (pairOverlapR0 i k * pairOverlapK0 j l +
        pairOverlapK0 i k * pairOverlapR0 j l)

def pairOverlapV1 : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
    pairOverlapPowerCoefficient i j * pairOverlapPowerCoefficient k l *
      (pairOverlapR1 i k * pairOverlapK1 j l +
        pairOverlapK1 i k * pairOverlapR1 j l)

theorem pairOverlapB0_exact :
    pairOverlapB0 =
      37135838084503969818181593775783850906481332145283057203510598690355221786462807949149679920294027407947102201 /
      1274211197009910226248787849656002209415895730202797484614644283054710345970362123668443972860659090220090000 := by
  norm_num [pairOverlapB0, pairOverlapK0, pairOverlapEtaQ, pairOverlapSQ,
    pairOverlapPowerCoefficient, Fin.sum_univ_succ]

theorem pairOverlapB1_exact :
    pairOverlapB1 =
      1186737005873220335326274298813716746763803984030123894677459384855656313152237467232737580354852451131979102201 /
      200730951027665962955707297472184660937721598525768567322791789080237012104060773151743022096000000000000000000 := by
  norm_num [pairOverlapB1, pairOverlapK1, pairOverlapEtaQ, pairOverlapSQ,
    pairOverlapPowerCoefficient, Fin.sum_univ_succ]

theorem pairOverlapV0_exact :
    pairOverlapV0 =
      -385913120935881187154548843107644751444282438299676226309349975939905231365526004158113040179906119774414730311828685202670246800 /
      16187170442316138686199253180555650391782548751436293046619304850493107705270913170375240258414907478022829905178692607537660517 := by
  norm_num [pairOverlapV0, pairOverlapR0, pairOverlapK0, pairOverlapShiftSum,
    pairOverlapEtaQ, pairOverlapSQ, pairOverlapPowerCoefficient, Fin.sum_univ_succ,
    Finset.sum_range_succ]

theorem pairOverlapV1_exact :
    pairOverlapV1 =
      -14222392786963076440621515271539465399584658768194956546792973202833271394483929513725066285891277986237177263660583828666743060811946108235900252225213579 /
      3712573712814705698860551842301628539046003210243942422522342253050919298037622765074959982812848643916696545782851500903871625371083216000000000000000000 := by
  norm_num [pairOverlapV1, pairOverlapR1, pairOverlapK1, pairOverlapShiftSum,
    pairOverlapEtaQ, pairOverlapSQ, pairOverlapPowerCoefficient, Fin.sum_univ_succ,
    Finset.sum_range_succ]

theorem pairOverlapB0_pos : 0 < pairOverlapB0 := by
  rw [pairOverlapB0_exact]
  norm_num

theorem pairOverlapB1_pos : 0 < pairOverlapB1 := by
  rw [pairOverlapB1_exact]
  norm_num

end UnitDistance.Witness

