module

public import UnitDistance.PairMassDegree3DenseData
public import UnitDistance.PairMassEndpointCertificate
public import UnitDistance.PairMassDegree3ScalarCertificateRun20260920b

@[expose] public section
set_option backward.privateInPublic true


/-!
# Dense exact arithmetic for the degree-3 pair-mass certificate

The polynomial computation is carried out in a fixed `10 x 10` array over
`ℚ`.  The accompanying representation lemmas connect that computation to the
nested real polynomial used by the analytic certificate.
-/

open scoped BigOperators

namespace UnitDistance.Witness

def pairMassPQ : ℚ := 4000000 / 2083647

def pairMassChooseQ : ℕ → ℚ
  | 0 => 1
  | k + 1 => pairMassChooseQ k * (pairMassPQ - k) / (k + 1)

abbrev PairMassDense3 := Vector (Vector ℚ 10) 10

def pairMassDenseOfFn (f : Fin 10 → Fin 10 → ℚ) : PairMassDense3 :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

def pairMassDenseGet (A : PairMassDense3) (i j : ℕ) : ℚ :=
  if hi : i < 10 then
    if hj : j < 10 then A.get ⟨i, hi⟩ |>.get ⟨j, hj⟩ else 0
  else 0

def pairMassDenseZero : PairMassDense3 := pairMassDenseOfFn fun _ _ => 0

def pairMassDenseOne : PairMassDense3 := pairMassDenseOfFn fun i j =>
  if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 1 else 0

def pairMassDenseAdd (A B : PairMassDense3) : PairMassDense3 :=
  pairMassDenseOfFn fun i j => pairMassDenseGet A i j + pairMassDenseGet B i j

def pairMassDenseScale (c : ℚ) (A : PairMassDense3) : PairMassDense3 :=
  pairMassDenseOfFn fun i j => c * pairMassDenseGet A i j

def pairMassDenseMul (A B : PairMassDense3) : PairMassDense3 :=
  pairMassDenseOfFn fun a b =>
    ∑ i ∈ Finset.range ((a : ℕ) + 1), ∑ j ∈ Finset.range ((b : ℕ) + 1),
      pairMassDenseGet A i j * pairMassDenseGet B ((a : ℕ) - i) ((b : ℕ) - j)

/-- Convolution specialized to a right factor supported in bidegrees at most
three.  The guards are placed before the rational products so the evaluator
does not normalize terms known to vanish. -/
def pairMassDenseMulCubic (A B : PairMassDense3) : PairMassDense3 :=
  pairMassDenseOfFn fun a b =>
    ∑ di ∈ Finset.range ((a : ℕ) + 1), ∑ dj ∈ Finset.range ((b : ℕ) + 1),
      if di < 4 ∧ dj < 4 then
        pairMassDenseGet A ((a : ℕ) - di) ((b : ℕ) - dj) *
          pairMassDenseGet B di dj
      else 0

def pairMassDensePow (A : PairMassDense3) : ℕ → PairMassDense3
  | 0 => pairMassDenseOne
  | k + 1 => pairMassDenseMul (pairMassDensePow A k) A

def pairMassDenseBase : PairMassDense3 := pairMassDenseOfFn fun a b =>
  if ha : (a : ℕ) < 4 then
    if hb : (b : ℕ) < 4 then pairPowerCoefficients ⟨a, ha⟩ ⟨b, hb⟩ else 0
  else 0

def pairMassPolynomialQ (t u : ℚ) : ℚ :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    pairPowerCoefficients a b * t ^ (a : ℕ) * u ^ (b : ℕ)

def pairMassCellCenterQ (i j : Fin 8) : ℚ :=
  (pairMassPolynomialQ ((i : ℕ) / 8) ((j : ℕ) / 8) +
    pairMassPolynomialQ (((i : ℕ) + 1) / 8) (((j : ℕ) + 1) / 8)) / 2

def pairMassCellRadiusQ (i j : Fin 8) : ℚ :=
  (pairMassPolynomialQ (((i : ℕ) + 1) / 8) (((j : ℕ) + 1) / 8) -
    pairMassPolynomialQ ((i : ℕ) / 8) ((j : ℕ) / 8)) /
  (pairMassPolynomialQ (((i : ℕ) + 1) / 8) (((j : ℕ) + 1) / 8) +
    pairMassPolynomialQ ((i : ℕ) / 8) ((j : ℕ) / 8))

def pairMassDenseCentered (i j : Fin 8) : PairMassDense3 :=
  pairMassDenseAdd
    (pairMassDenseScale (pairMassCellCenterQ i j)⁻¹ pairMassDenseBase)
    (pairMassDenseScale (-1) pairMassDenseOne)

def pairMassDenseSquare (i j : Fin 8) : PairMassDense3 :=
  pairMassDenseMulCubic (pairMassDenseCentered i j) (pairMassDenseCentered i j)

def pairMassDenseCube (i j : Fin 8) : PairMassDense3 :=
  pairMassDenseMulCubic (pairMassDenseSquare i j) (pairMassDenseCentered i j)

def pairMassDenseBaseSquare : PairMassDense3 :=
  pairMassDenseMulCubic pairMassDenseBase pairMassDenseBase

def pairMassDenseBaseCube : PairMassDense3 :=
  pairMassDenseMulCubic pairMassDenseBaseSquare pairMassDenseBase

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
theorem pairMassDenseBaseSquare_eq_data :
    pairMassDenseBaseSquare = pairMassDenseBaseSquareData := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
theorem pairMassDenseBaseCube_eq_data :
    pairMassDenseBaseCube = pairMassDenseBaseCubeData := by
  decide +kernel

def pairMassTailQ (i j : Fin 8) : ℚ :=
  |pairMassChooseQ 4| * pairMassCellRadiusQ i j ^ 4 /
    (1 - pairMassCellRadiusQ i j)

def pairMassBracketConstantQ (i j : Fin 8) : ℚ :=
  pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + pairMassTailQ i j

def pairMassBracketLinearQ (i j : Fin 8) : ℚ :=
  (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    (pairMassCellCenterQ i j)⁻¹

def pairMassBracketQuadraticQ (i j : Fin 8) : ℚ :=
  (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) *
    (pairMassCellCenterQ i j)⁻¹ ^ 2

def pairMassBracketCubicQ (i j : Fin 8) : ℚ :=
  pairMassChooseQ 3 * (pairMassCellCenterQ i j)⁻¹ ^ 3

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
theorem pairMassCellCenterQ_eq_data (i j : Fin 8) :
    pairMassCellCenterQ i j = pairMassCellCenterDataQ3 i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/- Scalar radius certificates generated by
verification/conditional-20260925/kernel-repair/generate-cell-certificates.py. -/

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_0_0 :
    pairMassCellRadiusQ 0 0 = pairMassCellRadiusDataQ3 0 0 := by
  change pairMassCellRadiusQ 0 0 = ((260463987730939 : ℚ) / 784751987730939)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_0_1 :
    pairMassCellRadiusQ 0 1 = pairMassCellRadiusDataQ3 0 1 := by
  change pairMassCellRadiusQ 0 1 = ((31786493831721 : ℚ) / 129399845653673)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_0_2 :
    pairMassCellRadiusQ 0 2 = pairMassCellRadiusDataQ3 0 2 := by
  change pairMassCellRadiusQ 0 2 = ((1314272674016917 : ℚ) / 6384501536296597)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_0_3 :
    pairMassCellRadiusQ 0 3 = pairMassCellRadiusDataQ3 0 3 := by
  change pairMassCellRadiusQ 0 3 = ((11133111207727 : ℚ) / 60040020051015)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_0_4 :
    pairMassCellRadiusQ 0 4 = pairMassCellRadiusDataQ3 0 4 := by
  change pairMassCellRadiusQ 0 4 = ((1598035968675387 : ℚ) / 9213696414273083)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_0_5 :
    pairMassCellRadiusQ 0 5 = pairMassCellRadiusDataQ3 0 5 := by
  change pairMassCellRadiusQ 0 5 = ((45688635249151 : ℚ) / 277651564423807)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_0_6 :
    pairMassCellRadiusQ 0 6 = pairMassCellRadiusDataQ3 0 6 := by
  change pairMassCellRadiusQ 0 6 = ((421569218430229 : ℚ) / 2699612110398741)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_0_7 :
    pairMassCellRadiusQ 0 7 = pairMassCellRadiusDataQ3 0 7 := by
  change pairMassCellRadiusQ 0 7 = ((2376189012618 : ℚ) / 16138212731273)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_1_0 :
    pairMassCellRadiusQ 1 0 = pairMassCellRadiusDataQ3 1 0 := by
  change pairMassCellRadiusQ 1 0 = ((31786493831721 : ℚ) / 129399845653673)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_1_1 :
    pairMassCellRadiusQ 1 1 = pairMassCellRadiusDataQ3 1 1 := by
  change pairMassCellRadiusQ 1 1 = ((1254303203965657 : ℚ) / 6480383081275047)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_1_2 :
    pairMassCellRadiusQ 1 2 = pairMassCellRadiusDataQ3 1 2 := by
  change pairMassCellRadiusQ 1 2 = ((16298777606209 : ℚ) / 96891947348906)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_1_3 :
    pairMassCellRadiusQ 1 3 = pairMassCellRadiusDataQ3 1 3 := by
  change pairMassCellRadiusQ 1 3 = ((1416862759631211 : ℚ) / 9115636969944725)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_1_4 :
    pairMassCellRadiusQ 1 4 = pairMassCellRadiusDataQ3 1 4 := by
  change pairMassCellRadiusQ 1 4 = ((198723856267289 : ℚ) / 1337493956407161)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_1_5 :
    pairMassCellRadiusQ 1 5 = pairMassCellRadiusDataQ3 1 5 := by
  change pairMassCellRadiusQ 1 5 = ((363858494557441 : ℚ) / 2526204971147135)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_1_6 :
    pairMassCellRadiusQ 1 6 = pairMassCellRadiusDataQ3 1 6 := by
  change pairMassCellRadiusQ 1 6 = ((131373351271692 : ℚ) / 939723850454087)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_1_7 :
    pairMassCellRadiusQ 1 7 = pairMassCellRadiusDataQ3 1 7 := by
  change pairMassCellRadiusQ 1 7 = ((9186567115423 : ℚ) / 68076780866913)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_2_0 :
    pairMassCellRadiusQ 2 0 = pairMassCellRadiusDataQ3 2 0 := by
  change pairMassCellRadiusQ 2 0 = ((1314272674016917 : ℚ) / 6384501536296597)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_2_1 :
    pairMassCellRadiusQ 2 1 = pairMassCellRadiusDataQ3 2 1 := by
  change pairMassCellRadiusQ 2 1 = ((16298777606209 : ℚ) / 96891947348906)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_2_2 :
    pairMassCellRadiusQ 2 2 = pairMassCellRadiusDataQ3 2 2 := by
  change pairMassCellRadiusQ 2 2 = ((1357213222542303 : ℚ) / 9091899507783007)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_2_3 :
    pairMassCellRadiusQ 2 3 = pairMassCellRadiusDataQ3 2 3 := by
  change pairMassCellRadiusQ 2 3 = ((184041090984377 : ℚ) / 1315948340535527)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_2_4 :
    pairMassCellRadiusQ 2 4 = pairMassCellRadiusDataQ3 2 4 := by
  change pairMassCellRadiusQ 2 4 = ((1647371736216209 : ℚ) / 12179871465792145)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_2_5 :
    pairMassCellRadiusQ 2 5 = pairMassCellRadiusDataQ3 2 5 := by
  change pairMassCellRadiusQ 2 5 = ((117529078705452 : ℚ) / 885637985042677)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_2_6 :
    pairMassCellRadiusQ 2 6 = pairMassCellRadiusDataQ3 2 6 := by
  change pairMassCellRadiusQ 2 6 = ((433946461761887 : ℚ) / 3324009927466463)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_2_7 :
    pairMassCellRadiusQ 2 7 = pairMassCellRadiusDataQ3 2 7 := by
  change pairMassCellRadiusQ 2 7 = ((314161987063021 : ℚ) / 2456356390514579)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_3_0 :
    pairMassCellRadiusQ 3 0 = pairMassCellRadiusDataQ3 3 0 := by
  change pairMassCellRadiusQ 3 0 = ((11133111207727 : ℚ) / 60040020051015)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_3_1 :
    pairMassCellRadiusQ 3 1 = pairMassCellRadiusDataQ3 3 1 := by
  change pairMassCellRadiusQ 3 1 = ((1416862759631211 : ℚ) / 9115636969944725)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_3_2 :
    pairMassCellRadiusQ 3 2 = pairMassCellRadiusDataQ3 3 2 := by
  change pairMassCellRadiusQ 3 2 = ((184041090984377 : ℚ) / 1315948340535527)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_3_3 :
    pairMassCellRadiusQ 3 3 = pairMassCellRadiusDataQ3 3 3 := by
  change pairMassCellRadiusQ 3 3 = ((318053345973421 : ℚ) / 2407875892038483)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_3_4 :
    pairMassCellRadiusQ 3 4 = pairMassCellRadiusDataQ3 3 4 := by
  change pairMassCellRadiusQ 3 4 = ((6912138109977 : ℚ) / 53786807844974)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_3_5 :
    pairMassCellRadiusQ 3 5 = pairMassCellRadiusDataQ3 3 5 := by
  change pairMassCellRadiusQ 3 5 = ((2008881197282671 : ℚ) / 15836124399291025)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_3_6 :
    pairMassCellRadiusQ 3 6 = pairMassCellRadiusDataQ3 3 6 := by
  change pairMassCellRadiusQ 3 6 = ((288402355474927 : ℚ) / 2294736482971185)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_3_7 :
    pairMassCellRadiusQ 3 7 = pairMassCellRadiusDataQ3 3 7 := by
  change pairMassCellRadiusQ 3 7 = ((2663350886250981 : ℚ) / 21453132832392731)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_4_0 :
    pairMassCellRadiusQ 4 0 = pairMassCellRadiusDataQ3 4 0 := by
  change pairMassCellRadiusQ 4 0 = ((1598035968675387 : ℚ) / 9213696414273083)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_4_1 :
    pairMassCellRadiusQ 4 1 = pairMassCellRadiusDataQ3 4 1 := by
  change pairMassCellRadiusQ 4 1 = ((198723856267289 : ℚ) / 1337493956407161)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_4_2 :
    pairMassCellRadiusQ 4 2 = pairMassCellRadiusDataQ3 4 2 := by
  change pairMassCellRadiusQ 4 2 = ((1647371736216209 : ℚ) / 12179871465792145)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_4_3 :
    pairMassCellRadiusQ 4 3 = pairMassCellRadiusDataQ3 4 3 := by
  change pairMassCellRadiusQ 4 3 = ((6912138109977 : ℚ) / 53786807844974)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_4_4 :
    pairMassCellRadiusQ 4 4 = pairMassCellRadiusDataQ3 4 4 := by
  change pairMassCellRadiusQ 4 4 = ((390985287839411 : ℚ) / 3116914525851315)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_4_5 :
    pairMassCellRadiusQ 4 5 = pairMassCellRadiusDataQ3 4 5 := by
  change pairMassCellRadiusQ 4 5 = ((275294714323759 : ℚ) / 2217660984882191)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_4_6 :
    pairMassCellRadiusQ 4 6 = pairMassCellRadiusDataQ3 4 6 := by
  change pairMassCellRadiusQ 4 6 = ((2510529911578197 : ℚ) / 20355535508151893)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_4_7 :
    pairMassCellRadiusQ 4 7 = pairMassCellRadiusDataQ3 4 7 := by
  change pairMassCellRadiusQ 4 7 = ((22485716870363 : ℚ) / 183931894273245)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_5_0 :
    pairMassCellRadiusQ 5 0 = pairMassCellRadiusDataQ3 5 0 := by
  change pairMassCellRadiusQ 5 0 = ((45688635249151 : ℚ) / 277651564423807)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_5_1 :
    pairMassCellRadiusQ 5 1 = pairMassCellRadiusDataQ3 5 1 := by
  change pairMassCellRadiusQ 5 1 = ((363858494557441 : ℚ) / 2526204971147135)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_5_2 :
    pairMassCellRadiusQ 5 2 = pairMassCellRadiusDataQ3 5 2 := by
  change pairMassCellRadiusQ 5 2 = ((117529078705452 : ℚ) / 885637985042677)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_5_3 :
    pairMassCellRadiusQ 5 3 = pairMassCellRadiusDataQ3 5 3 := by
  change pairMassCellRadiusQ 5 3 = ((2008881197282671 : ℚ) / 15836124399291025)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_5_4 :
    pairMassCellRadiusQ 5 4 = pairMassCellRadiusDataQ3 5 4 := by
  change pairMassCellRadiusQ 5 4 = ((275294714323759 : ℚ) / 2217660984882191)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_5_5 :
    pairMassCellRadiusQ 5 5 = pairMassCellRadiusDataQ3 5 5 := by
  change pairMassCellRadiusQ 5 5 = ((1318344364089 : ℚ) / 10722901505351)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_5_6 :
    pairMassCellRadiusQ 5 6 = pairMassCellRadiusDataQ3 5 6 := by
  change pairMassCellRadiusQ 5 6 = ((34697027480087 : ℚ) / 283992597400682)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_5_7 :
    pairMassCellRadiusQ 5 7 = pairMassCellRadiusDataQ3 5 7 := by
  change pairMassCellRadiusQ 5 7 = ((3151325020549547 : ℚ) / 26017390440279637)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_6_0 :
    pairMassCellRadiusQ 6 0 = pairMassCellRadiusDataQ3 6 0 := by
  change pairMassCellRadiusQ 6 0 = ((421569218430229 : ℚ) / 2699612110398741)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_6_1 :
    pairMassCellRadiusQ 6 1 = pairMassCellRadiusDataQ3 6 1 := by
  change pairMassCellRadiusQ 6 1 = ((131373351271692 : ℚ) / 939723850454087)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_6_2 :
    pairMassCellRadiusQ 6 2 = pairMassCellRadiusDataQ3 6 2 := by
  change pairMassCellRadiusQ 6 2 = ((433946461761887 : ℚ) / 3324009927466463)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_6_3 :
    pairMassCellRadiusQ 6 3 = pairMassCellRadiusDataQ3 6 3 := by
  change pairMassCellRadiusQ 6 3 = ((288402355474927 : ℚ) / 2294736482971185)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_6_4 :
    pairMassCellRadiusQ 6 4 = pairMassCellRadiusDataQ3 6 4 := by
  change pairMassCellRadiusQ 6 4 = ((2510529911578197 : ℚ) / 20355535508151893)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_6_5 :
    pairMassCellRadiusQ 6 5 = pairMassCellRadiusDataQ3 6 5 := by
  change pairMassCellRadiusQ 6 5 = ((34697027480087 : ℚ) / 283992597400682)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_6_6 :
    pairMassCellRadiusQ 6 6 = pairMassCellRadiusDataQ3 6 6 := by
  change pairMassCellRadiusQ 6 6 = ((3099012390546887 : ℚ) / 25555935937052487)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_6_7 :
    pairMassCellRadiusQ 6 7 = pairMassCellRadiusDataQ3 6 7 := by
  change pairMassCellRadiusQ 6 7 = ((86909429356479 : ℚ) / 724288679118017)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_7_0 :
    pairMassCellRadiusQ 7 0 = pairMassCellRadiusDataQ3 7 0 := by
  change pairMassCellRadiusQ 7 0 = ((2376189012618 : ℚ) / 16138212731273)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_7_1 :
    pairMassCellRadiusQ 7 1 = pairMassCellRadiusDataQ3 7 1 := by
  change pairMassCellRadiusQ 7 1 = ((9186567115423 : ℚ) / 68076780866913)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_7_2 :
    pairMassCellRadiusQ 7 2 = pairMassCellRadiusDataQ3 7 2 := by
  change pairMassCellRadiusQ 7 2 = ((314161987063021 : ℚ) / 2456356390514579)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_7_3 :
    pairMassCellRadiusQ 7 3 = pairMassCellRadiusDataQ3 7 3 := by
  change pairMassCellRadiusQ 7 3 = ((2663350886250981 : ℚ) / 21453132832392731)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_7_4 :
    pairMassCellRadiusQ 7 4 = pairMassCellRadiusDataQ3 7 4 := by
  change pairMassCellRadiusQ 7 4 = ((22485716870363 : ℚ) / 183931894273245)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_7_5 :
    pairMassCellRadiusQ 7 5 = pairMassCellRadiusDataQ3 7 5 := by
  change pairMassCellRadiusQ 7 5 = ((3151325020549547 : ℚ) / 26017390440279637)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_7_6 :
    pairMassCellRadiusQ 7 6 = pairMassCellRadiusDataQ3 7 6 := by
  change pairMassCellRadiusQ 7 6 = ((86909429356479 : ℚ) / 724288679118017)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
private theorem pairMassCellRadiusScalar_7_7 :
    pairMassCellRadiusQ 7 7 = pairMassCellRadiusDataQ3 7 7 := by
  change pairMassCellRadiusQ 7 7 = ((3846894725114233 : ℚ) / 32501843052713607)
  norm_num [pairMassCellRadiusQ, pairMassPolynomialQ,
    pairPowerCoefficients, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
theorem pairMassCellRadiusQ_eq_data (i j : Fin 8) :
    pairMassCellRadiusQ i j = pairMassCellRadiusDataQ3 i j := by
  fin_cases i <;> fin_cases j
  · exact pairMassCellRadiusScalar_0_0
  · exact pairMassCellRadiusScalar_0_1
  · exact pairMassCellRadiusScalar_0_2
  · exact pairMassCellRadiusScalar_0_3
  · exact pairMassCellRadiusScalar_0_4
  · exact pairMassCellRadiusScalar_0_5
  · exact pairMassCellRadiusScalar_0_6
  · exact pairMassCellRadiusScalar_0_7
  · exact pairMassCellRadiusScalar_1_0
  · exact pairMassCellRadiusScalar_1_1
  · exact pairMassCellRadiusScalar_1_2
  · exact pairMassCellRadiusScalar_1_3
  · exact pairMassCellRadiusScalar_1_4
  · exact pairMassCellRadiusScalar_1_5
  · exact pairMassCellRadiusScalar_1_6
  · exact pairMassCellRadiusScalar_1_7
  · exact pairMassCellRadiusScalar_2_0
  · exact pairMassCellRadiusScalar_2_1
  · exact pairMassCellRadiusScalar_2_2
  · exact pairMassCellRadiusScalar_2_3
  · exact pairMassCellRadiusScalar_2_4
  · exact pairMassCellRadiusScalar_2_5
  · exact pairMassCellRadiusScalar_2_6
  · exact pairMassCellRadiusScalar_2_7
  · exact pairMassCellRadiusScalar_3_0
  · exact pairMassCellRadiusScalar_3_1
  · exact pairMassCellRadiusScalar_3_2
  · exact pairMassCellRadiusScalar_3_3
  · exact pairMassCellRadiusScalar_3_4
  · exact pairMassCellRadiusScalar_3_5
  · exact pairMassCellRadiusScalar_3_6
  · exact pairMassCellRadiusScalar_3_7
  · exact pairMassCellRadiusScalar_4_0
  · exact pairMassCellRadiusScalar_4_1
  · exact pairMassCellRadiusScalar_4_2
  · exact pairMassCellRadiusScalar_4_3
  · exact pairMassCellRadiusScalar_4_4
  · exact pairMassCellRadiusScalar_4_5
  · exact pairMassCellRadiusScalar_4_6
  · exact pairMassCellRadiusScalar_4_7
  · exact pairMassCellRadiusScalar_5_0
  · exact pairMassCellRadiusScalar_5_1
  · exact pairMassCellRadiusScalar_5_2
  · exact pairMassCellRadiusScalar_5_3
  · exact pairMassCellRadiusScalar_5_4
  · exact pairMassCellRadiusScalar_5_5
  · exact pairMassCellRadiusScalar_5_6
  · exact pairMassCellRadiusScalar_5_7
  · exact pairMassCellRadiusScalar_6_0
  · exact pairMassCellRadiusScalar_6_1
  · exact pairMassCellRadiusScalar_6_2
  · exact pairMassCellRadiusScalar_6_3
  · exact pairMassCellRadiusScalar_6_4
  · exact pairMassCellRadiusScalar_6_5
  · exact pairMassCellRadiusScalar_6_6
  · exact pairMassCellRadiusScalar_6_7
  · exact pairMassCellRadiusScalar_7_0
  · exact pairMassCellRadiusScalar_7_1
  · exact pairMassCellRadiusScalar_7_2
  · exact pairMassCellRadiusScalar_7_3
  · exact pairMassCellRadiusScalar_7_4
  · exact pairMassCellRadiusScalar_7_5
  · exact pairMassCellRadiusScalar_7_6
  · exact pairMassCellRadiusScalar_7_7

/- Exact bracket scalar certificates. Generated by
verification/conditional-20260925/kernel-repair/generate-bracket-certificates.py.
Each table lookup is converted definitionally to a rational literal; norm_num
then proves the scalar equality. Splitting the proof avoids monolithic
rational reduction during independent kernel checking. -/
section
set_option maxHeartbeats 1000000000
set_option maxRecDepth 100000

private theorem pairMassBracketScalarCase_0_0_0 :
    pairMassBracketConstantQ 0 0 = pairMassBracketScalarDataQ3 0 0 0 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((260463987730939 : ℚ) / 784751987730939) ^ 4 /
    (1 - ((260463987730939 : ℚ) / 784751987730939)) =
    ((-188833351800720647933880636172039884611636702910357736738180567543755603794029 : ℚ) / 14327981955718586969611624247423160807692055570532890898813170657724054634496000)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_0_1 :
    pairMassBracketConstantQ 0 1 = pairMassBracketScalarDataQ3 0 0 1 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((31786493831721 : ℚ) / 129399845653673) ^ 4 /
    (1 - ((31786493831721 : ℚ) / 129399845653673)) =
    ((-2878951138428515290138945697043597202058247288701452415821584596132853938947 : ℚ) / 217042713428924598201698842886494494212949335069409334669957414481386454076678)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_0_2 :
    pairMassBracketConstantQ 0 2 = pairMassBracketScalarDataQ3 0 0 2 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1314272674016917 : ℚ) / 6384501536296597) ^ 4 /
    (1 - ((1314272674016917 : ℚ) / 6384501536296597)) =
    ((-40217070529449632925337955557389040460689173614736352151782305038612768770874062357 : ℚ) / 3028207858266969989786786453856599443780597730237602544666228170429811997379644240768)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_0_3 :
    pairMassBracketConstantQ 0 3 = pairMassBracketScalarDataQ3 0 0 3 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((11133111207727 : ℚ) / 60040020051015) ^ 4 /
    (1 - ((11133111207727 : ℚ) / 60040020051015)) =
    ((-7952510041372795607968244670134230778993104278866894221828226599373830600429 : ℚ) / 598563919929005964462036623339116769561768806367401191310561924335149535428571)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_0_4 :
    pairMassBracketConstantQ 0 4 = pairMassBracketScalarDataQ3 0 0 4 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1598035968675387 : ℚ) / 9213696414273083) ^ 4 /
    (1 - ((1598035968675387 : ℚ) / 9213696414273083)) =
    ((-23312772514111881851155877740815482073031007336035663688050964289004512919521494359367 : ℚ) / 1754388911621249458823525171999990467840804865855486987358447355788477790087466408875008)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_0_5 :
    pairMassBracketConstantQ 0 5 = pairMassBracketScalarDataQ3 0 0 5 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((45688635249151 : ℚ) / 277651564423807) ^ 4 /
    (1 - ((45688635249151 : ℚ) / 277651564423807)) =
    ((-8328602179364763490305259654904378478561216571737501230817043892614169577344797 : ℚ) / 626698679841224992589648780917868969786145767322991083327251418066864258559077078)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_0_6 :
    pairMassBracketConstantQ 0 6 = pairMassBracketScalarDataQ3 0 0 6 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((421569218430229 : ℚ) / 2699612110398741) ^ 4 /
    (1 - ((421569218430229 : ℚ) / 2699612110398741)) =
    ((-526324099578722543341386292307552423549159821717452890363691909225051511928321726101 : ℚ) / 39600791029438401721857389825911703945948332540196675808367980470376919228598032977024)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_0_7 :
    pairMassBracketConstantQ 0 7 = pairMassBracketScalarDataQ3 0 0 7 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((2376189012618 : ℚ) / 16138212731273) ^ 4 /
    (1 - ((2376189012618 : ℚ) / 16138212731273)) =
    ((-2898388483315276532439516355774807908151994730339982362274423875128860553413 : ℚ) / 218059587345716706403367751663616966151624398092004763428158247779700263046587)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_1_0 :
    pairMassBracketConstantQ 1 0 = pairMassBracketScalarDataQ3 0 1 0 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((31786493831721 : ℚ) / 129399845653673) ^ 4 /
    (1 - ((31786493831721 : ℚ) / 129399845653673)) =
    ((-2878951138428515290138945697043597202058247288701452415821584596132853938947 : ℚ) / 217042713428924598201698842886494494212949335069409334669957414481386454076678)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_1_1 :
    pairMassBracketConstantQ 1 1 = pairMassBracketScalarDataQ3 0 1 1 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1254303203965657 : ℚ) / 6480383081275047) ^ 4 /
    (1 - ((1254303203965657 : ℚ) / 6480383081275047)) =
    ((-44758643031917152582316389274227138584599937492991816231125353626320842436526856867 : ℚ) / 3369329604623485920184646512913686035523430976779590531172703708175485714860027843133)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_1_2 :
    pairMassBracketConstantQ 1 2 = pairMassBracketScalarDataQ3 0 1 2 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((16298777606209 : ℚ) / 96891947348906) ^ 4 /
    (1 - ((16298777606209 : ℚ) / 96891947348906)) =
    ((-6886281211870359763794770239174305261461564314571176183510356458142120215556233 : ℚ) / 518190132222309691199272630134852352492049530919692403790578348314114456562068767)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_1_3 :
    pairMassBracketConstantQ 1 3 = pairMassBracketScalarDataQ3 0 1 3 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1416862759631211 : ℚ) / 9115636969944725) ^ 4 /
    (1 - ((1416862759631211 : ℚ) / 9115636969944725)) =
    ((-103658495073987984703610067151486056125819507283385942051119098611393258254859453 : ℚ) / 7799246789746773526955848584674360130407937099754303358733359951692612194540685923)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_1_4 :
    pairMassBracketConstantQ 1 4 = pairMassBracketScalarDataQ3 0 1 4 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((198723856267289 : ℚ) / 1337493956407161) ^ 4 /
    (1 - ((198723856267289 : ℚ) / 1337493956407161)) =
    ((-9142360470774378137267853646223952273316087641903645709993262012995421194823004551 : ℚ) / 687830385535473714636519546274238279530110568174389402100571816589990428110920839199)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_1_5 :
    pairMassBracketConstantQ 1 5 = pairMassBracketScalarDataQ3 0 1 5 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((363858494557441 : ℚ) / 2526204971147135) ^ 4 /
    (1 - ((363858494557441 : ℚ) / 2526204971147135)) =
    ((-104809429192805284868401001997001225282055161209491760956807132781569003444522089057 : ℚ) / 7885130141216942226695546971768523914301683360967664707084415953388895960271747546943)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_1_6 :
    pairMassBracketConstantQ 1 6 = pairMassBracketScalarDataQ3 0 1 6 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((131373351271692 : ℚ) / 939723850454087) ^ 4 /
    (1 - ((131373351271692 : ℚ) / 939723850454087)) =
    ((-33614818847793916057521745412210004877315207889298819530627637141488350472897612503 : ℚ) / 2528873091617369793198233383540627574457453185488435554159831282201223676979157987497)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_1_7 :
    pairMassBracketConstantQ 1 7 = pairMassBracketScalarDataQ3 0 1 7 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((9186567115423 : ℚ) / 68076780866913) ^ 4 /
    (1 - ((9186567115423 : ℚ) / 68076780866913)) =
    ((-18137760857446919456120702262598390498399377432442489757091703357644155794973 : ℚ) / 1364480313208472579105273392465879207798244682849417629350421459407456255905027)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_2_0 :
    pairMassBracketConstantQ 2 0 = pairMassBracketScalarDataQ3 0 2 0 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1314272674016917 : ℚ) / 6384501536296597) ^ 4 /
    (1 - ((1314272674016917 : ℚ) / 6384501536296597)) =
    ((-40217070529449632925337955557389040460689173614736352151782305038612768770874062357 : ℚ) / 3028207858266969989786786453856599443780597730237602544666228170429811997379644240768)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_2_1 :
    pairMassBracketConstantQ 2 1 = pairMassBracketScalarDataQ3 0 2 1 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((16298777606209 : ℚ) / 96891947348906) ^ 4 /
    (1 - ((16298777606209 : ℚ) / 96891947348906)) =
    ((-6886281211870359763794770239174305261461564314571176183510356458142120215556233 : ℚ) / 518190132222309691199272630134852352492049530919692403790578348314114456562068767)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_2_2 :
    pairMassBracketConstantQ 2 2 = pairMassBracketScalarDataQ3 0 2 2 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1357213222542303 : ℚ) / 9091899507783007) ^ 4 /
    (1 - ((1357213222542303 : ℚ) / 9091899507783007)) =
    ((-22756099095734255721521996805997470500101872821213791918744063949823099605422984646237 : ℚ) / 1712076595980804407745672108497635218841125167992240646494949266866087937964693062338138)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_2_3 :
    pairMassBracketConstantQ 2 3 = pairMassBracketScalarDataQ3 0 2 3 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((184041090984377 : ℚ) / 1315948340535527) ^ 4 /
    (1 - ((184041090984377 : ℚ) / 1315948340535527)) =
    ((-38777408720422927017095300885175169042290915584621204617490588565454440433327054613 : ℚ) / 2917260384216392063358744599280969094823875975387662449704464405192180428049771525387)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_2_4 :
    pairMassBracketConstantQ 2 4 = pairMassBracketScalarDataQ3 0 2 4 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1647371736216209 : ℚ) / 12179871465792145) ^ 4 /
    (1 - ((1647371736216209 : ℚ) / 12179871465792145)) =
    ((-255449474431312632589144547321244401839321611173131566074641081425583768440531377711 : ℚ) / 19217167711169173614526900448246866888011073039672129045169197574423222553471782345664)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_2_5 :
    pairMassBracketConstantQ 2 5 = pairMassBracketScalarDataQ3 0 2 5 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((117529078705452 : ℚ) / 885637985042677) ^ 4 /
    (1 - ((117529078705452 : ℚ) / 885637985042677)) =
    ((-5347734537807720609917232276097198111491041046458204844337276868293042315270280003 : ℚ) / 402298189445625091355285646683614149723446739775924000867443156327457754146606439997)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_2_6 :
    pairMassBracketConstantQ 2 6 = pairMassBracketScalarDataQ3 0 2 6 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((433946461761887 : ℚ) / 3324009927466463) ^ 4 /
    (1 - ((433946461761887 : ℚ) / 3324009927466463)) =
    ((-178098721558859333249351397277174483309973078257459175240300816251995505704802529773 : ℚ) / 13397819962421383789450978585712967792846813501356604256476583500185200945356371892102)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_2_7 :
    pairMassBracketConstantQ 2 7 = pairMassBracketScalarDataQ3 0 2 7 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((314161987063021 : ℚ) / 2456356390514579) ^ 4 /
    (1 - ((314161987063021 : ℚ) / 2456356390514579)) =
    ((-1704728266904577118944675637185693864448473830097620359409189856395555015209614373931 : ℚ) / 128239794978632112187623097105046341261795342844170879537040744484736884427084797126069)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_3_0 :
    pairMassBracketConstantQ 3 0 = pairMassBracketScalarDataQ3 0 3 0 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((11133111207727 : ℚ) / 60040020051015) ^ 4 /
    (1 - ((11133111207727 : ℚ) / 60040020051015)) =
    ((-7952510041372795607968244670134230778993104278866894221828226599373830600429 : ℚ) / 598563919929005964462036623339116769561768806367401191310561924335149535428571)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_3_1 :
    pairMassBracketConstantQ 3 1 = pairMassBracketScalarDataQ3 0 3 1 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1416862759631211 : ℚ) / 9115636969944725) ^ 4 /
    (1 - ((1416862759631211 : ℚ) / 9115636969944725)) =
    ((-103658495073987984703610067151486056125819507283385942051119098611393258254859453 : ℚ) / 7799246789746773526955848584674360130407937099754303358733359951692612194540685923)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_3_2 :
    pairMassBracketConstantQ 3 2 = pairMassBracketScalarDataQ3 0 3 2 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((184041090984377 : ℚ) / 1315948340535527) ^ 4 /
    (1 - ((184041090984377 : ℚ) / 1315948340535527)) =
    ((-38777408720422927017095300885175169042290915584621204617490588565454440433327054613 : ℚ) / 2917260384216392063358744599280969094823875975387662449704464405192180428049771525387)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_3_3 :
    pairMassBracketConstantQ 3 3 = pairMassBracketScalarDataQ3 0 3 3 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((318053345973421 : ℚ) / 2407875892038483) ^ 4 /
    (1 - ((318053345973421 : ℚ) / 2407875892038483)) =
    ((-10965356004636008865302362233101986046786080143534552546257472807781761325770873550829 : ℚ) / 824896660163924012539382681978486901380475745726571056517830942360720205597462102949171)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_3_4 :
    pairMassBracketConstantQ 3 4 = pairMassBracketScalarDataQ3 0 3 4 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((6912138109977 : ℚ) / 53786807844974) ^ 4 /
    (1 - ((6912138109977 : ℚ) / 53786807844974)) =
    ((-228456328640414578416907800731918599243496466930153142633690533268321763805829 : ℚ) / 17185893865383009318725891618361523225970185445182151240902425994654973586069171)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_3_5 :
    pairMassBracketConstantQ 3 5 = pairMassBracketScalarDataQ3 0 3 5 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((2008881197282671 : ℚ) / 15836124399291025) ^ 4 /
    (1 - ((2008881197282671 : ℚ) / 15836124399291025)) =
    ((-42611116896091992361079040340796661042016047121446576600684439785710134515560884907 : ℚ) / 3205445778774046312792259092126554383851638460924111885832926337392661652540351739701)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_3_6 :
    pairMassBracketConstantQ 3 6 = pairMassBracketScalarDataQ3 0 3 6 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((288402355474927 : ℚ) / 2294736482971185) ^ 4 /
    (1 - ((288402355474927 : ℚ) / 2294736482971185)) =
    ((-946728918936663177375091320480530054541835482757014677937948229768350510807322517 : ℚ) / 71217844121635421622333903812265255855589482646385031955011861868558454462435385483)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_3_7 :
    pairMassBracketConstantQ 3 7 = pairMassBracketScalarDataQ3 0 3 7 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((2663350886250981 : ℚ) / 21453132832392731) ^ 4 /
    (1 - ((2663350886250981 : ℚ) / 21453132832392731)) =
    ((-185947458033387034062693926696939350703734254190331426244844176718594434157472274948443 : ℚ) / 13987834243513391397963272068342284243115439811154879162674472357920118554894863100583557)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_4_0 :
    pairMassBracketConstantQ 4 0 = pairMassBracketScalarDataQ3 0 4 0 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1598035968675387 : ℚ) / 9213696414273083) ^ 4 /
    (1 - ((1598035968675387 : ℚ) / 9213696414273083)) =
    ((-23312772514111881851155877740815482073031007336035663688050964289004512919521494359367 : ℚ) / 1754388911621249458823525171999990467840804865855486987358447355788477790087466408875008)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_4_1 :
    pairMassBracketConstantQ 4 1 = pairMassBracketScalarDataQ3 0 4 1 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((198723856267289 : ℚ) / 1337493956407161) ^ 4 /
    (1 - ((198723856267289 : ℚ) / 1337493956407161)) =
    ((-9142360470774378137267853646223952273316087641903645709993262012995421194823004551 : ℚ) / 687830385535473714636519546274238279530110568174389402100571816589990428110920839199)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_4_2 :
    pairMassBracketConstantQ 4 2 = pairMassBracketScalarDataQ3 0 4 2 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1647371736216209 : ℚ) / 12179871465792145) ^ 4 /
    (1 - ((1647371736216209 : ℚ) / 12179871465792145)) =
    ((-255449474431312632589144547321244401839321611173131566074641081425583768440531377711 : ℚ) / 19217167711169173614526900448246866888011073039672129045169197574423222553471782345664)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_4_3 :
    pairMassBracketConstantQ 4 3 = pairMassBracketScalarDataQ3 0 4 3 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((6912138109977 : ℚ) / 53786807844974) ^ 4 /
    (1 - ((6912138109977 : ℚ) / 53786807844974)) =
    ((-228456328640414578416907800731918599243496466930153142633690533268321763805829 : ℚ) / 17185893865383009318725891618361523225970185445182151240902425994654973586069171)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_4_4 :
    pairMassBracketConstantQ 4 4 = pairMassBracketScalarDataQ3 0 4 4 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((390985287839411 : ℚ) / 3116914525851315) ^ 4 /
    (1 - ((390985287839411 : ℚ) / 3116914525851315)) =
    ((-1108042337342237387279164410486865209915075881301894658814487294681273385184110367 : ℚ) / 83352583384156596824964220764102793613769476138865864577640769755801503872441883008)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_4_5 :
    pairMassBracketConstantQ 4 5 = pairMassBracketScalarDataQ3 0 4 5 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((275294714323759 : ℚ) / 2217660984882191) ^ 4 /
    (1 - ((275294714323759 : ℚ) / 2217660984882191)) =
    ((-21636968063780425413207632966280605970692632708769583476374362593869461467101619689 : ℚ) / 1627633487866847768950581564162101065100051680014515211268383986033048546265856724061)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_4_6 :
    pairMassBracketConstantQ 4 6 = pairMassBracketScalarDataQ3 0 4 6 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((2510529911578197 : ℚ) / 20355535508151893) ^ 4 /
    (1 - ((2510529911578197 : ℚ) / 20355535508151893)) =
    ((-84182949536599650953135870867711120458884316542511260561580581998438266327059605213441 : ℚ) / 6332611588414755647829467225182998409704805771519132809086000717283728895072792591677184)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_4_7 :
    pairMassBracketConstantQ 4 7 = pairMassBracketScalarDataQ3 0 4 7 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((22485716870363 : ℚ) / 183931894273245) ^ 4 /
    (1 - ((22485716870363 : ℚ) / 183931894273245)) =
    ((-3020786172104315910257836791077505415557662736480281072859075602839683071458213 : ℚ) / 227235784331749150296393210048346929710777352482206399760383700166629856878177787)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_5_0 :
    pairMassBracketConstantQ 5 0 = pairMassBracketScalarDataQ3 0 5 0 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((45688635249151 : ℚ) / 277651564423807) ^ 4 /
    (1 - ((45688635249151 : ℚ) / 277651564423807)) =
    ((-8328602179364763490305259654904378478561216571737501230817043892614169577344797 : ℚ) / 626698679841224992589648780917868969786145767322991083327251418066864258559077078)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_5_1 :
    pairMassBracketConstantQ 5 1 = pairMassBracketScalarDataQ3 0 5 1 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((363858494557441 : ℚ) / 2526204971147135) ^ 4 /
    (1 - ((363858494557441 : ℚ) / 2526204971147135)) =
    ((-104809429192805284868401001997001225282055161209491760956807132781569003444522089057 : ℚ) / 7885130141216942226695546971768523914301683360967664707084415953388895960271747546943)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_5_2 :
    pairMassBracketConstantQ 5 2 = pairMassBracketScalarDataQ3 0 5 2 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((117529078705452 : ℚ) / 885637985042677) ^ 4 /
    (1 - ((117529078705452 : ℚ) / 885637985042677)) =
    ((-5347734537807720609917232276097198111491041046458204844337276868293042315270280003 : ℚ) / 402298189445625091355285646683614149723446739775924000867443156327457754146606439997)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_5_3 :
    pairMassBracketConstantQ 5 3 = pairMassBracketScalarDataQ3 0 5 3 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((2008881197282671 : ℚ) / 15836124399291025) ^ 4 /
    (1 - ((2008881197282671 : ℚ) / 15836124399291025)) =
    ((-42611116896091992361079040340796661042016047121446576600684439785710134515560884907 : ℚ) / 3205445778774046312792259092126554383851638460924111885832926337392661652540351739701)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_5_4 :
    pairMassBracketConstantQ 5 4 = pairMassBracketScalarDataQ3 0 5 4 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((275294714323759 : ℚ) / 2217660984882191) ^ 4 /
    (1 - ((275294714323759 : ℚ) / 2217660984882191)) =
    ((-21636968063780425413207632966280605970692632708769583476374362593869461467101619689 : ℚ) / 1627633487866847768950581564162101065100051680014515211268383986033048546265856724061)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_5_5 :
    pairMassBracketConstantQ 5 5 = pairMassBracketScalarDataQ3 0 5 5 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((1318344364089 : ℚ) / 10722901505351) ^ 4 /
    (1 - ((1318344364089 : ℚ) / 10722901505351)) =
    ((-207532368932622211720514385907690610315214263865196806896335665520760493577 : ℚ) / 15611471646251672079047501319292555310685909539740970136004591817920830006423)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_5_6 :
    pairMassBracketConstantQ 5 6 = pairMassBracketScalarDataQ3 0 5 6 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((34697027480087 : ℚ) / 283992597400682) ^ 4 /
    (1 - ((34697027480087 : ℚ) / 283992597400682)) =
    ((-9755379603129143545345021060836264119906933501882273682073936126129152203643413 : ℚ) / 733838983536512749109710505279848924404356003603301147533914157610467031033331587)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_5_7 :
    pairMassBracketConstantQ 5 7 = pairMassBracketScalarDataQ3 0 5 7 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((3151325020549547 : ℚ) / 26017390440279637) ^ 4 /
    (1 - ((3151325020549547 : ℚ) / 26017390440279637)) =
    ((-4324617432197561133093134440445942928372436810191623617614939758061778315342710534080527 : ℚ) / 325313764978849729286057721483311758654102259441953578368085163737514589898264181074619473)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_6_0 :
    pairMassBracketConstantQ 6 0 = pairMassBracketScalarDataQ3 0 6 0 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((421569218430229 : ℚ) / 2699612110398741) ^ 4 /
    (1 - ((421569218430229 : ℚ) / 2699612110398741)) =
    ((-526324099578722543341386292307552423549159821717452890363691909225051511928321726101 : ℚ) / 39600791029438401721857389825911703945948332540196675808367980470376919228598032977024)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_6_1 :
    pairMassBracketConstantQ 6 1 = pairMassBracketScalarDataQ3 0 6 1 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((131373351271692 : ℚ) / 939723850454087) ^ 4 /
    (1 - ((131373351271692 : ℚ) / 939723850454087)) =
    ((-33614818847793916057521745412210004877315207889298819530627637141488350472897612503 : ℚ) / 2528873091617369793198233383540627574457453185488435554159831282201223676979157987497)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_6_2 :
    pairMassBracketConstantQ 6 2 = pairMassBracketScalarDataQ3 0 6 2 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((433946461761887 : ℚ) / 3324009927466463) ^ 4 /
    (1 - ((433946461761887 : ℚ) / 3324009927466463)) =
    ((-178098721558859333249351397277174483309973078257459175240300816251995505704802529773 : ℚ) / 13397819962421383789450978585712967792846813501356604256476583500185200945356371892102)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_6_3 :
    pairMassBracketConstantQ 6 3 = pairMassBracketScalarDataQ3 0 6 3 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((288402355474927 : ℚ) / 2294736482971185) ^ 4 /
    (1 - ((288402355474927 : ℚ) / 2294736482971185)) =
    ((-946728918936663177375091320480530054541835482757014677937948229768350510807322517 : ℚ) / 71217844121635421622333903812265255855589482646385031955011861868558454462435385483)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_6_4 :
    pairMassBracketConstantQ 6 4 = pairMassBracketScalarDataQ3 0 6 4 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((2510529911578197 : ℚ) / 20355535508151893) ^ 4 /
    (1 - ((2510529911578197 : ℚ) / 20355535508151893)) =
    ((-84182949536599650953135870867711120458884316542511260561580581998438266327059605213441 : ℚ) / 6332611588414755647829467225182998409704805771519132809086000717283728895072792591677184)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_6_5 :
    pairMassBracketConstantQ 6 5 = pairMassBracketScalarDataQ3 0 6 5 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((34697027480087 : ℚ) / 283992597400682) ^ 4 /
    (1 - ((34697027480087 : ℚ) / 283992597400682)) =
    ((-9755379603129143545345021060836264119906933501882273682073936126129152203643413 : ℚ) / 733838983536512749109710505279848924404356003603301147533914157610467031033331587)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_6_6 :
    pairMassBracketConstantQ 6 6 = pairMassBracketScalarDataQ3 0 6 6 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((3099012390546887 : ℚ) / 25555935937052487) ^ 4 /
    (1 - ((3099012390546887 : ℚ) / 25555935937052487)) =
    ((-176103705803315992350702309752481812419864966302779812900898739096570627995479136894911 : ℚ) / 13247181456060926985621076301321378336223243163322558585863763486498068392517122417923214)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_6_7 :
    pairMassBracketConstantQ 6 7 = pairMassBracketScalarDataQ3 0 6 7 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((86909429356479 : ℚ) / 724288679118017) ^ 4 /
    (1 - ((86909429356479 : ℚ) / 724288679118017)) =
    ((-30342180991685589989802157799467803564703941678274763382638437755614844374652112543 : ℚ) / 2282441191920078686475861133429065072382243949163073897075449960472958619385073387457)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_7_0 :
    pairMassBracketConstantQ 7 0 = pairMassBracketScalarDataQ3 0 7 0 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((2376189012618 : ℚ) / 16138212731273) ^ 4 /
    (1 - ((2376189012618 : ℚ) / 16138212731273)) =
    ((-2898388483315276532439516355774807908151994730339982362274423875128860553413 : ℚ) / 218059587345716706403367751663616966151624398092004763428158247779700263046587)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_7_1 :
    pairMassBracketConstantQ 7 1 = pairMassBracketScalarDataQ3 0 7 1 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((9186567115423 : ℚ) / 68076780866913) ^ 4 /
    (1 - ((9186567115423 : ℚ) / 68076780866913)) =
    ((-18137760857446919456120702262598390498399377432442489757091703357644155794973 : ℚ) / 1364480313208472579105273392465879207798244682849417629350421459407456255905027)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_7_2 :
    pairMassBracketConstantQ 7 2 = pairMassBracketScalarDataQ3 0 7 2 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((314161987063021 : ℚ) / 2456356390514579) ^ 4 /
    (1 - ((314161987063021 : ℚ) / 2456356390514579)) =
    ((-1704728266904577118944675637185693864448473830097620359409189856395555015209614373931 : ℚ) / 128239794978632112187623097105046341261795342844170879537040744484736884427084797126069)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_7_3 :
    pairMassBracketConstantQ 7 3 = pairMassBracketScalarDataQ3 0 7 3 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((2663350886250981 : ℚ) / 21453132832392731) ^ 4 /
    (1 - ((2663350886250981 : ℚ) / 21453132832392731)) =
    ((-185947458033387034062693926696939350703734254190331426244844176718594434157472274948443 : ℚ) / 13987834243513391397963272068342284243115439811154879162674472357920118554894863100583557)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_7_4 :
    pairMassBracketConstantQ 7 4 = pairMassBracketScalarDataQ3 0 7 4 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((22485716870363 : ℚ) / 183931894273245) ^ 4 /
    (1 - ((22485716870363 : ℚ) / 183931894273245)) =
    ((-3020786172104315910257836791077505415557662736480281072859075602839683071458213 : ℚ) / 227235784331749150296393210048346929710777352482206399760383700166629856878177787)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_7_5 :
    pairMassBracketConstantQ 7 5 = pairMassBracketScalarDataQ3 0 7 5 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((3151325020549547 : ℚ) / 26017390440279637) ^ 4 /
    (1 - ((3151325020549547 : ℚ) / 26017390440279637)) =
    ((-4324617432197561133093134440445942928372436810191623617614939758061778315342710534080527 : ℚ) / 325313764978849729286057721483311758654102259441953578368085163737514589898264181074619473)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_7_6 :
    pairMassBracketConstantQ 7 6 = pairMassBracketScalarDataQ3 0 7 6 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((86909429356479 : ℚ) / 724288679118017) ^ 4 /
    (1 - ((86909429356479 : ℚ) / 724288679118017)) =
    ((-30342180991685589989802157799467803564703941678274763382638437755614844374652112543 : ℚ) / 2282441191920078686475861133429065072382243949163073897075449960472958619385073387457)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_0_7_7 :
    pairMassBracketConstantQ 7 7 = pairMassBracketScalarDataQ3 0 7 7 := by
  simp only [pairMassBracketConstantQ, pairMassTailQ, pairMassCellRadiusQ_eq_data]
  change pairMassChooseQ 0 - pairMassChooseQ 1 + pairMassChooseQ 2 -
    pairMassChooseQ 3 + |pairMassChooseQ 4| * ((3846894725114233 : ℚ) / 32501843052713607) ^ 4 /
    (1 - ((3846894725114233 : ℚ) / 32501843052713607)) =
    ((-33617750870426002707901956229069468699564493480469042536256718153039170507294539922162967 : ℚ) / 2528824848828289040066982969267213060688563959668843341467121894935719587145613391143337033)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_0_0 :
    pairMassBracketLinearQ 0 0 = pairMassBracketScalarDataQ3 1 0 0 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((784751987730939 : ℚ) / 524288000000000)⁻¹ =
    ((394861135689416704000000000000000 : ℚ) / 7099125595689092260905822172470597)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_0_1 :
    pairMassBracketLinearQ 0 1 = pairMassBracketScalarDataQ3 1 0 1 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((129399845653673 : ℚ) / 65536000000000)⁻¹ =
    ((7051091708739584000000000000000 : ℚ) / 167227675698872985264611525392497)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_0_2 :
    pairMassBracketLinearQ 0 2 = pairMassBracketScalarDataQ3 1 0 2 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((6384501536296597 : ℚ) / 2621440000000000)⁻¹ =
    ((282043668349583360000000000000000 : ℚ) / 8250901282125741966917318582425533)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_0_3 :
    pairMassBracketLinearQ 0 3 = pairMassBracketScalarDataQ3 1 0 3 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((12008004010203 : ℚ) / 4096000000000)⁻¹ =
    ((3084852622573568000000000000000 : ℚ) / 108628369159603885849084520877669)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_0_4 :
    pairMassBracketLinearQ 0 4 = pairMassBracketScalarDataQ3 1 0 4 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((9213696414273083 : ℚ) / 2621440000000000)⁻¹ =
    ((1974305678447083520000000000000000 : ℚ) / 83350140003597067354964790562203909)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_0_5 :
    pairMassBracketLinearQ 0 5 = pairMassBracketScalarDataQ3 1 0 5 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((277651564423807 : ℚ) / 65536000000000)⁻¹ =
    ((7051091708739584000000000000000 : ℚ) / 358818246947663167710601054559223)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_0_6 :
    pairMassBracketLinearQ 0 6 = pairMassBracketScalarDataQ3 1 0 6 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2699612110398741 : ℚ) / 524288000000000)⁻¹ =
    ((394861135689416704000000000000000 : ℚ) / 24421582526701219542263916220592043)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_0_7 :
    pairMassBracketLinearQ 0 7 = pairMassBracketScalarDataQ3 1 0 7 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((16138212731273 : ℚ) / 2560000000000)⁻¹ =
    ((1928032889108480000000000000000 : ℚ) / 145991600990421925359290646132279)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_1_0 :
    pairMassBracketLinearQ 1 0 = pairMassBracketScalarDataQ3 1 1 0 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((129399845653673 : ℚ) / 65536000000000)⁻¹ =
    ((7051091708739584000000000000000 : ℚ) / 167227675698872985264611525392497)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_1_1 :
    pairMassBracketLinearQ 1 1 = pairMassBracketScalarDataQ3 1 1 1 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((6480383081275047 : ℚ) / 2621440000000000)⁻¹ =
    ((282043668349583360000000000000000 : ℚ) / 8374812155652413870920157770847583)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_1_2 :
    pairMassBracketLinearQ 1 2 = pairMassBracketScalarDataQ3 1 1 2 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((48445973674453 : ℚ) / 16384000000000)⁻¹ =
    ((12339410490294272000000000000000 : ℚ) / 438258274075640117953691077405419)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_1_3 :
    pairMassBracketLinearQ 1 3 = pairMassBracketScalarDataQ3 1 1 3 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((364625478797789 : ℚ) / 104857600000000)⁻¹ =
    ((7179293376171212800000000000000 : ℚ) / 299865679608282475228225324714377)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_1_4 :
    pairMassBracketLinearQ 1 4 = pairMassBracketScalarDataQ3 1 1 4 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((1337493956407161 : ℚ) / 327680000000000)⁻¹ =
    ((35255458543697920000000000000000 : ℚ) / 1728487421769274321913885952686529)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_1_5 :
    pairMassBracketLinearQ 1 5 = pairMassBracketScalarDataQ3 1 1 5 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((505240994229427 : ℚ) / 104857600000000)⁻¹ =
    ((78972227137883340800000000000000 : ℚ) / 4570576857659765695042394110663821)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_1_6 :
    pairMassBracketLinearQ 1 6 = pairMassBracketScalarDataQ3 1 1 6 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((939723850454087 : ℚ) / 163840000000000)⁻¹ =
    ((123394104902942720000000000000000 : ℚ) / 8501052235531793826226938485291001)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_1_7 :
    pairMassBracketLinearQ 1 7 = pairMassBracketScalarDataQ3 1 1 7 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((3608069385946389 : ℚ) / 524288000000000)⁻¹ =
    ((56408733669916672000000000000000 : ℚ) / 4662826714545991944088955301839421)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_2_0 :
    pairMassBracketLinearQ 2 0 = pairMassBracketScalarDataQ3 1 2 0 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((6384501536296597 : ℚ) / 2621440000000000)⁻¹ =
    ((282043668349583360000000000000000 : ℚ) / 8250901282125741966917318582425533)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_2_1 :
    pairMassBracketLinearQ 2 1 = pairMassBracketScalarDataQ3 1 2 1 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((48445973674453 : ℚ) / 16384000000000)⁻¹ =
    ((12339410490294272000000000000000 : ℚ) / 438258274075640117953691077405419)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_2_2 :
    pairMassBracketLinearQ 2 2 = pairMassBracketScalarDataQ3 1 2 2 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((9091899507783007 : ℚ) / 2621440000000000)⁻¹ =
    ((1974305678447083520000000000000000 : ℚ) / 82248324971768304526728820254376161)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_2_3 :
    pairMassBracketLinearQ 2 3 = pairMassBracketScalarDataQ3 1 2 3 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((1315948340535527 : ℚ) / 327680000000000)⁻¹ =
    ((246788209805885440000000000000000 : ℚ) / 11904503197134153783695249009804121)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_2_4 :
    pairMassBracketLinearQ 2 4 = pairMassBracketScalarDataQ3 1 2 4 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2435974293158429 : ℚ) / 524288000000000)⁻¹ =
    ((394861135689416704000000000000000 : ℚ) / 22036627782242515127963221249992867)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_2_5 :
    pairMassBracketLinearQ 2 5 = pairMassBracketScalarDataQ3 1 2 5 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((885637985042677 : ℚ) / 163840000000000)⁻¹ =
    ((123394104902942720000000000000000 : ℚ) / 8011773638586357511013573822618571)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_2_6 :
    pairMassBracketLinearQ 2 6 = pairMassBracketScalarDataQ3 1 2 6 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((3324009927466463 : ℚ) / 524288000000000)⁻¹ =
    ((394861135689416704000000000000000 : ℚ) / 30070091347755208683498247041431649)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_2_7 :
    pairMassBracketLinearQ 2 7 = pairMassBracketScalarDataQ3 1 2 7 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2456356390514579 : ℚ) / 327680000000000)⁻¹ =
    ((35255458543697920000000000000000 : ℚ) / 3174430137831980801827933692476331)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_3_0 :
    pairMassBracketLinearQ 3 0 = pairMassBracketScalarDataQ3 1 3 0 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((12008004010203 : ℚ) / 4096000000000)⁻¹ =
    ((3084852622573568000000000000000 : ℚ) / 108628369159603885849084520877669)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_3_1 :
    pairMassBracketLinearQ 3 1 = pairMassBracketScalarDataQ3 1 3 1 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((364625478797789 : ℚ) / 104857600000000)⁻¹ =
    ((7179293376171212800000000000000 : ℚ) / 299865679608282475228225324714377)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_3_2 :
    pairMassBracketLinearQ 3 2 = pairMassBracketScalarDataQ3 1 3 2 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((1315948340535527 : ℚ) / 327680000000000)⁻¹ =
    ((246788209805885440000000000000000 : ℚ) / 11904503197134153783695249009804121)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_3_3 :
    pairMassBracketLinearQ 3 3 = pairMassBracketScalarDataQ3 1 3 3 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2407875892038483 : ℚ) / 524288000000000)⁻¹ =
    ((394861135689416704000000000000000 : ℚ) / 21782440367992932335904261508208109)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_3_4 :
    pairMassBracketLinearQ 3 4 = pairMassBracketScalarDataQ3 1 3 4 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((26893403922487 : ℚ) / 5120000000000)⁻¹ =
    ((3856065778216960000000000000000 : ℚ) / 243286611727311525211615315464201)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_3_5 :
    pairMassBracketLinearQ 3 5 = pairMassBracketScalarDataQ3 1 3 5 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((633444975971641 : ℚ) / 104857600000000)⁻¹ =
    ((2547491197996236800000000000000 : ℚ) / 184850077669369385737737193344153)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_3_6 :
    pairMassBracketLinearQ 3 6 = pairMassBracketScalarDataQ3 1 3 6 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((458947296594237 : ℚ) / 65536000000000)⁻¹ =
    ((4487058360107008000000000000000 : ℚ) / 377435343935294333603241564424041)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_3_7 :
    pairMassBracketLinearQ 3 7 = pairMassBracketScalarDataQ3 1 3 7 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((21453132832392731 : ℚ) / 2621440000000000)⁻¹ =
    ((1974305678447083520000000000000000 : ℚ) / 194072123141119725415094062865643813)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_4_0 :
    pairMassBracketLinearQ 4 0 = pairMassBracketScalarDataQ3 1 4 0 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((9213696414273083 : ℚ) / 2621440000000000)⁻¹ =
    ((1974305678447083520000000000000000 : ℚ) / 83350140003597067354964790562203909)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_4_1 :
    pairMassBracketLinearQ 4 1 = pairMassBracketScalarDataQ3 1 4 1 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((1337493956407161 : ℚ) / 327680000000000)⁻¹ =
    ((35255458543697920000000000000000 : ℚ) / 1728487421769274321913885952686529)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_4_2 :
    pairMassBracketLinearQ 4 2 = pairMassBracketScalarDataQ3 1 4 2 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2435974293158429 : ℚ) / 524288000000000)⁻¹ =
    ((394861135689416704000000000000000 : ℚ) / 22036627782242515127963221249992867)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_4_3 :
    pairMassBracketLinearQ 4 3 = pairMassBracketScalarDataQ3 1 4 3 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((26893403922487 : ℚ) / 5120000000000)⁻¹ =
    ((3856065778216960000000000000000 : ℚ) / 243286611727311525211615315464201)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_4_4 :
    pairMassBracketLinearQ 4 4 = pairMassBracketScalarDataQ3 1 4 4 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((623382905170263 : ℚ) / 104857600000000)⁻¹ =
    ((11281746733983334400000000000000 : ℚ) / 805618227559879603132783950917007)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_4_5 :
    pairMassBracketLinearQ 4 5 = pairMassBracketScalarDataQ3 1 4 5 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2217660984882191 : ℚ) / 327680000000000)⁻¹ =
    ((246788209805885440000000000000000 : ℚ) / 20061693511423207159369166023161393)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_4_6 :
    pairMassBracketLinearQ 4 6 = pairMassBracketScalarDataQ3 1 4 6 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((20355535508151893 : ℚ) / 2621440000000000)⁻¹ =
    ((282043668349583360000000000000000 : ℚ) / 26306127904855781971994603442718077)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_4_7 :
    pairMassBracketLinearQ 4 7 = pairMassBracketScalarDataQ3 1 4 7 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((36786378854649 : ℚ) / 4096000000000)⁻¹ =
    ((3084852622573568000000000000000 : ℚ) / 332781729492469020079266642825927)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_5_0 :
    pairMassBracketLinearQ 5 0 = pairMassBracketScalarDataQ3 1 5 0 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((277651564423807 : ℚ) / 65536000000000)⁻¹ =
    ((7051091708739584000000000000000 : ℚ) / 358818246947663167710601054559223)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_5_1 :
    pairMassBracketLinearQ 5 1 = pairMassBracketScalarDataQ3 1 5 1 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((505240994229427 : ℚ) / 104857600000000)⁻¹ =
    ((78972227137883340800000000000000 : ℚ) / 4570576857659765695042394110663821)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_5_2 :
    pairMassBracketLinearQ 5 2 = pairMassBracketScalarDataQ3 1 5 2 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((885637985042677 : ℚ) / 163840000000000)⁻¹ =
    ((123394104902942720000000000000000 : ℚ) / 8011773638586357511013573822618571)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_5_3 :
    pairMassBracketLinearQ 5 3 = pairMassBracketScalarDataQ3 1 5 3 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((633444975971641 : ℚ) / 104857600000000)⁻¹ =
    ((2547491197996236800000000000000 : ℚ) / 184850077669369385737737193344153)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_5_4 :
    pairMassBracketLinearQ 5 4 = pairMassBracketScalarDataQ3 1 5 4 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2217660984882191 : ℚ) / 327680000000000)⁻¹ =
    ((246788209805885440000000000000000 : ℚ) / 20061693511423207159369166023161393)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_5_5 :
    pairMassBracketLinearQ 5 5 = pairMassBracketScalarDataQ3 1 5 5 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((3999642261495923 : ℚ) / 524288000000000)⁻¹ =
    ((56408733669916672000000000000000 : ℚ) / 5168869218028792107089835302052747)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_5_6 :
    pairMassBracketLinearQ 5 6 = pairMassBracketScalarDataQ3 1 5 6 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((141996298700341 : ℚ) / 16384000000000)⁻¹ =
    ((12339410490294272000000000000000 : ℚ) / 1284545403333627043460156821128843)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_5_7 :
    pairMassBracketLinearQ 5 7 = pairMassBracketScalarDataQ3 1 5 7 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((26017390440279637 : ℚ) / 2621440000000000)⁻¹ =
    ((282043668349583360000000000000000 : ℚ) / 33623129217036617211243134284404093)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_6_0 :
    pairMassBracketLinearQ 6 0 = pairMassBracketScalarDataQ3 1 6 0 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2699612110398741 : ℚ) / 524288000000000)⁻¹ =
    ((394861135689416704000000000000000 : ℚ) / 24421582526701219542263916220592043)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_6_1 :
    pairMassBracketLinearQ 6 1 = pairMassBracketScalarDataQ3 1 6 1 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((939723850454087 : ℚ) / 163840000000000)⁻¹ =
    ((123394104902942720000000000000000 : ℚ) / 8501052235531793826226938485291001)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_6_2 :
    pairMassBracketLinearQ 6 2 = pairMassBracketScalarDataQ3 1 6 2 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((3324009927466463 : ℚ) / 524288000000000)⁻¹ =
    ((394861135689416704000000000000000 : ℚ) / 30070091347755208683498247041431649)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_6_3 :
    pairMassBracketLinearQ 6 3 = pairMassBracketScalarDataQ3 1 6 3 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((458947296594237 : ℚ) / 65536000000000)⁻¹ =
    ((4487058360107008000000000000000 : ℚ) / 377435343935294333603241564424041)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_6_4 :
    pairMassBracketLinearQ 6 4 = pairMassBracketScalarDataQ3 1 6 4 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((20355535508151893 : ℚ) / 2621440000000000)⁻¹ =
    ((282043668349583360000000000000000 : ℚ) / 26306127904855781971994603442718077)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_6_5 :
    pairMassBracketLinearQ 6 5 = pairMassBracketScalarDataQ3 1 6 5 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((141996298700341 : ℚ) / 16384000000000)⁻¹ =
    ((12339410490294272000000000000000 : ℚ) / 1284545403333627043460156821128843)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_6_6 :
    pairMassBracketLinearQ 6 6 = pairMassBracketScalarDataQ3 1 6 6 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((25555935937052487 : ℚ) / 2621440000000000)⁻¹ =
    ((1974305678447083520000000000000000 : ℚ) / 231187434716920448714940939107454201)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_6_7 :
    pairMassBracketLinearQ 6 7 = pairMassBracketScalarDataQ3 1 6 7 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((724288679118017 : ℚ) / 65536000000000)⁻¹ =
    ((49357641961177088000000000000000 : ℚ) / 6552154541795805539210895404891391)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_7_0 :
    pairMassBracketLinearQ 7 0 = pairMassBracketScalarDataQ3 1 7 0 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((16138212731273 : ℚ) / 2560000000000)⁻¹ =
    ((1928032889108480000000000000000 : ℚ) / 145991600990421925359290646132279)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_7_1 :
    pairMassBracketLinearQ 7 1 = pairMassBracketScalarDataQ3 1 7 1 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((3608069385946389 : ℚ) / 524288000000000)⁻¹ =
    ((56408733669916672000000000000000 : ℚ) / 4662826714545991944088955301839421)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_7_2 :
    pairMassBracketLinearQ 7 2 = pairMassBracketScalarDataQ3 1 7 2 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((2456356390514579 : ℚ) / 327680000000000)⁻¹ =
    ((35255458543697920000000000000000 : ℚ) / 3174430137831980801827933692476331)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_7_3 :
    pairMassBracketLinearQ 7 3 = pairMassBracketScalarDataQ3 1 7 3 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((21453132832392731 : ℚ) / 2621440000000000)⁻¹ =
    ((1974305678447083520000000000000000 : ℚ) / 194072123141119725415094062865643813)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_7_4 :
    pairMassBracketLinearQ 7 4 = pairMassBracketScalarDataQ3 1 7 4 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((36786378854649 : ℚ) / 4096000000000)⁻¹ =
    ((3084852622573568000000000000000 : ℚ) / 332781729492469020079266642825927)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_7_5 :
    pairMassBracketLinearQ 7 5 = pairMassBracketScalarDataQ3 1 7 5 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((26017390440279637 : ℚ) / 2621440000000000)⁻¹ =
    ((282043668349583360000000000000000 : ℚ) / 33623129217036617211243134284404093)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_7_6 :
    pairMassBracketLinearQ 7 6 = pairMassBracketScalarDataQ3 1 7 6 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((724288679118017 : ℚ) / 65536000000000)⁻¹ =
    ((49357641961177088000000000000000 : ℚ) / 6552154541795805539210895404891391)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_1_7_7 :
    pairMassBracketLinearQ 7 7 = pairMassBracketScalarDataQ3 1 7 7 := by
  simp only [pairMassBracketLinearQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 1 - 2 * pairMassChooseQ 2 + 3 * pairMassChooseQ 3) *
    ((32501843052713607 : ℚ) / 2621440000000000)⁻¹ =
    ((1974305678447083520000000000000000 : ℚ) / 294022403931391929389360167606379961)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_0_0 :
    pairMassBracketQuadraticQ 0 0 = pairMassBracketScalarDataQ3 2 0 0 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((784751987730939 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((2371425325383570763546624000000000000000000000000 : ℚ) / 5571052922368601549759555777809198447749724700583)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_0_1 :
    pairMassBracketQuadraticQ 0 1 = pairMassBracketScalarDataQ3 2 0 1 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((129399845653673 : ℚ) / 65536000000000)⁻¹ ^ 2 =
    ((5293360101302613311488000000000000000000000000 : ℚ) / 21639235424456647425037416267877085600854691481)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_0_2 :
    pairMassBracketQuadraticQ 0 2 = pairMassBracketScalarDataQ3 2 0 2 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((6384501536296597 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((8469376162084181298380800000000000000000000000000 : ℚ) / 52677891911563361500497930364658933983710353811201)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_0_3 :
    pairMassBracketQuadraticQ 0 3 = pairMassBracketScalarDataQ3 2 0 3 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((12008004010203 : ℚ) / 4096000000000)⁻¹ ^ 2 =
    ((144740315269993332736000000000000000000000000 : ℚ) / 1304409892490335350226788770355342229190856807)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_0_4 :
    pairMassBracketQuadraticQ 0 4 = pairMassBracketScalarDataQ3 2 0 4 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((9213696414273083 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((59285633134589269088665600000000000000000000000000 : ℚ) / 767962886080301752871957853843735050191180656081447)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_0_5 :
    pairMassBracketQuadraticQ 0 5 = pairMassBracketScalarDataQ3 2 0 5 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((277651564423807 : ℚ) / 65536000000000)⁻¹ ^ 2 =
    ((5293360101302613311488000000000000000000000000 : ℚ) / 99626447608826589444190966296344297704352621961)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_0_6 :
    pairMassBracketQuadraticQ 0 6 = pairMassBracketScalarDataQ3 2 0 6 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2699612110398741 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((2371425325383570763546624000000000000000000000000 : ℚ) / 65928799944184896866343696026637566870155821817863)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_0_7 :
    pairMassBracketQuadraticQ 0 7 = pairMassBracketScalarDataQ3 2 0 7 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((16138212731273 : ℚ) / 2560000000000)⁻¹ ^ 2 =
    ((56539185652341145600000000000000000000000000 : ℚ) / 2356043513762555031965221240164247214238061167)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_1_0 :
    pairMassBracketQuadraticQ 1 0 = pairMassBracketScalarDataQ3 2 1 0 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((129399845653673 : ℚ) / 65536000000000)⁻¹ ^ 2 =
    ((5293360101302613311488000000000000000000000000 : ℚ) / 21639235424456647425037416267877085600854691481)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_1_1 :
    pairMassBracketQuadraticQ 1 1 = pairMassBracketScalarDataQ3 2 1 1 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((6480383081275047 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((8469376162084181298380800000000000000000000000000 : ℚ) / 54271991002346508324896437798006328537341538161401)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_1_2 :
    pairMassBracketQuadraticQ 1 2 = pairMassBracketScalarDataQ3 2 1 2 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((48445973674453 : ℚ) / 16384000000000)⁻¹ ^ 2 =
    ((2315845044319893323776000000000000000000000000 : ℚ) / 21231848808479668837239037660544647157004060807)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_1_3 :
    pairMassBracketQuadraticQ 1 3 = pairMassBracketScalarDataQ3 2 1 3 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((364625478797789 : ℚ) / 104857600000000)⁻¹ ^ 2 =
    ((8623364819576620958351360000000000000000000000 : ℚ) / 109338667002194390958126885745535580675764112453)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_1_4 :
    pairMassBracketQuadraticQ 1 4 = pairMassBracketScalarDataQ3 2 1 4 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((1337493956407161 : ℚ) / 327680000000000)⁻¹ ^ 2 =
    ((132334002532565332787200000000000000000000000000 : ℚ) / 2311841480342199899200820316376314218500523834169)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_1_5 :
    pairMassBracketQuadraticQ 1 5 = pairMassBracketScalarDataQ3 2 1 5 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((505240994229427 : ℚ) / 104857600000000)⁻¹ ^ 2 =
    ((94857013015342830541864960000000000000000000000 : ℚ) / 2309242795766030270292627136728026275505342460567)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_1_6 :
    pairMassBracketQuadraticQ 1 6 = pairMassBracketScalarDataQ3 2 1 6 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((939723850454087 : ℚ) / 163840000000000)⁻¹ ^ 2 =
    ((231584504431989332377600000000000000000000000000 : ℚ) / 7988641539685261398264135270280739646044184771087)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_1_7 :
    pairMassBracketQuadraticQ 1 7 = pairMassBracketScalarDataQ3 2 1 7 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((3608069385946389 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((338775046483367251935232000000000000000000000000 : ℚ) / 16823802320726375619476458111174651415378592800769)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_2_0 :
    pairMassBracketQuadraticQ 2 0 = pairMassBracketScalarDataQ3 2 2 0 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((6384501536296597 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((8469376162084181298380800000000000000000000000000 : ℚ) / 52677891911563361500497930364658933983710353811201)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_2_1 :
    pairMassBracketQuadraticQ 2 1 = pairMassBracketScalarDataQ3 2 2 1 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((48445973674453 : ℚ) / 16384000000000)⁻¹ ^ 2 =
    ((2315845044319893323776000000000000000000000000 : ℚ) / 21231848808479668837239037660544647157004060807)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_2_2 :
    pairMassBracketQuadraticQ 2 2 = pairMassBracketScalarDataQ3 2 2 2 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((9091899507783007 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((59285633134589269088665600000000000000000000000000 : ℚ) / 747793505326797051035961014016014586149370941696127)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_2_3 :
    pairMassBracketQuadraticQ 2 3 = pairMassBracketScalarDataQ3 2 2 3 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((1315948340535527 : ℚ) / 327680000000000)⁻¹ ^ 2 =
    ((926338017727957329510400000000000000000000000000 : ℚ) / 15665711227168565312610143973659342371582511506767)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_2_4 :
    pairMassBracketQuadraticQ 2 4 = pairMassBracketScalarDataQ3 2 2 4 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2435974293158429 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((2371425325383570763546624000000000000000000000000 : ℚ) / 53680658785443609646294911843662035624783150925943)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_2_5 :
    pairMassBracketQuadraticQ 2 5 = pairMassBracketScalarDataQ3 2 2 5 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((885637985042677 : ℚ) / 163840000000000)⁻¹ ^ 2 =
    ((231584504431989332377600000000000000000000000000 : ℚ) / 7095531061895658378117626807410184934047327754567)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_2_6 :
    pairMassBracketQuadraticQ 2 6 = pairMassBracketScalarDataQ3 2 2 6 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((3324009927466463 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((2371425325383570763546624000000000000000000000000 : ℚ) / 99953282159761707850252712160947824377666954287487)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_2_7 :
    pairMassBracketQuadraticQ 2 7 = pairMassBracketScalarDataQ3 2 2 7 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2456356390514579 : ℚ) / 327680000000000)⁻¹ ^ 2 =
    ((132334002532565332787200000000000000000000000000 : ℚ) / 7797531755305661874822811455034346867145867929649)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_3_0 :
    pairMassBracketQuadraticQ 3 0 = pairMassBracketScalarDataQ3 2 3 0 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((12008004010203 : ℚ) / 4096000000000)⁻¹ ^ 2 =
    ((144740315269993332736000000000000000000000000 : ℚ) / 1304409892490335350226788770355342229190856807)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_3_1 :
    pairMassBracketQuadraticQ 3 1 = pairMassBracketScalarDataQ3 2 3 1 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((364625478797789 : ℚ) / 104857600000000)⁻¹ ^ 2 =
    ((8623364819576620958351360000000000000000000000 : ℚ) / 109338667002194390958126885745535580675764112453)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_3_2 :
    pairMassBracketQuadraticQ 3 2 = pairMassBracketScalarDataQ3 2 3 2 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((1315948340535527 : ℚ) / 327680000000000)⁻¹ ^ 2 =
    ((926338017727957329510400000000000000000000000000 : ℚ) / 15665711227168565312610143973659342371582511506767)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_3_3 :
    pairMassBracketQuadraticQ 3 3 = pairMassBracketScalarDataQ3 2 3 3 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2407875892038483 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((2371425325383570763546624000000000000000000000000 : ℚ) / 52449413031856043850692589320760469475628600658647)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_3_4 :
    pairMassBracketQuadraticQ 3 4 = pairMassBracketScalarDataQ3 2 3 4 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((26893403922487 : ℚ) / 5120000000000)⁻¹ ^ 2 =
    ((226156742609364582400000000000000000000000000 : ℚ) / 6542805118115851546553057917638267082627387887)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_3_5 :
    pairMassBracketQuadraticQ 3 5 = pairMassBracketScalarDataQ3 2 3 5 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((633444975971641 : ℚ) / 104857600000000)⁻¹ ^ 2 =
    ((3059903645656220340060160000000000000000000000 : ℚ) / 117092353007629663131150032322057867759281165073)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_3_6 :
    pairMassBracketQuadraticQ 3 6 = pairMassBracketScalarDataQ3 2 3 6 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((458947296594237 : ℚ) / 65536000000000)⁻¹ ^ 2 =
    ((3368501882647117561856000000000000000000000000 : ℚ) / 173222930738219379845407151744612871861784851717)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_3_7 :
    pairMassBracketQuadraticQ 3 7 = pairMassBracketScalarDataQ3 2 3 7 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((21453132832392731 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((59285633134589269088665600000000000000000000000000 : ℚ) / 4163455036810920689538714359313210595891255576323303)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_4_0 :
    pairMassBracketQuadraticQ 4 0 = pairMassBracketScalarDataQ3 2 4 0 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((9213696414273083 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((59285633134589269088665600000000000000000000000000 : ℚ) / 767962886080301752871957853843735050191180656081447)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_4_1 :
    pairMassBracketQuadraticQ 4 1 = pairMassBracketScalarDataQ3 2 4 1 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((1337493956407161 : ℚ) / 327680000000000)⁻¹ ^ 2 =
    ((132334002532565332787200000000000000000000000000 : ℚ) / 2311841480342199899200820316376314218500523834169)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_4_2 :
    pairMassBracketQuadraticQ 4 2 = pairMassBracketScalarDataQ3 2 4 2 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2435974293158429 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((2371425325383570763546624000000000000000000000000 : ℚ) / 53680658785443609646294911843662035624783150925943)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_4_3 :
    pairMassBracketQuadraticQ 4 3 = pairMassBracketScalarDataQ3 2 4 3 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((26893403922487 : ℚ) / 5120000000000)⁻¹ ^ 2 =
    ((226156742609364582400000000000000000000000000 : ℚ) / 6542805118115851546553057917638267082627387887)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_4_4 :
    pairMassBracketQuadraticQ 4 4 = pairMassBracketScalarDataQ3 2 4 4 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((623382905170263 : ℚ) / 104857600000000)⁻¹ ^ 2 =
    ((13551001859334690077409280000000000000000000000 : ℚ) / 502208631154395784730189740928218431400317362841)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_4_5 :
    pairMassBracketQuadraticQ 4 5 = pairMassBracketScalarDataQ3 2 4 5 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2217660984882191 : ℚ) / 327680000000000)⁻¹ ^ 2 =
    ((926338017727957329510400000000000000000000000000 : ℚ) / 44490034990947450290018420089314505534329484452063)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_4_6 :
    pairMassBracketQuadraticQ 4 6 = pairMassBracketScalarDataQ3 2 4 6 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((20355535508151893 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((8469376162084181298380800000000000000000000000000 : ℚ) / 535475320649277232235894671253699036707702892869761)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_4_7 :
    pairMassBracketQuadraticQ 4 7 = pairMassBracketScalarDataQ3 2 4 7 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((36786378854649 : ℚ) / 4096000000000)⁻¹ ^ 2 =
    ((144740315269993332736000000000000000000000000 : ℚ) / 12241834777015285854934648227510695846941684623)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_5_0 :
    pairMassBracketQuadraticQ 5 0 = pairMassBracketScalarDataQ3 2 5 0 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((277651564423807 : ℚ) / 65536000000000)⁻¹ ^ 2 =
    ((5293360101302613311488000000000000000000000000 : ℚ) / 99626447608826589444190966296344297704352621961)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_5_1 :
    pairMassBracketQuadraticQ 5 1 = pairMassBracketScalarDataQ3 2 5 1 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((505240994229427 : ℚ) / 104857600000000)⁻¹ ^ 2 =
    ((94857013015342830541864960000000000000000000000 : ℚ) / 2309242795766030270292627136728026275505342460567)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_5_2 :
    pairMassBracketQuadraticQ 5 2 = pairMassBracketScalarDataQ3 2 5 2 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((885637985042677 : ℚ) / 163840000000000)⁻¹ ^ 2 =
    ((231584504431989332377600000000000000000000000000 : ℚ) / 7095531061895658378117626807410184934047327754567)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_5_3 :
    pairMassBracketQuadraticQ 5 3 = pairMassBracketScalarDataQ3 2 5 3 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((633444975971641 : ℚ) / 104857600000000)⁻¹ ^ 2 =
    ((3059903645656220340060160000000000000000000000 : ℚ) / 117092353007629663131150032322057867759281165073)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_5_4 :
    pairMassBracketQuadraticQ 5 4 = pairMassBracketScalarDataQ3 2 5 4 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2217660984882191 : ℚ) / 327680000000000)⁻¹ ^ 2 =
    ((926338017727957329510400000000000000000000000000 : ℚ) / 44490034990947450290018420089314505534329484452063)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_5_5 :
    pairMassBracketQuadraticQ 5 5 = pairMassBracketScalarDataQ3 2 5 5 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((3999642261495923 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((338775046483367251935232000000000000000000000000 : ℚ) / 20673627768573341155512235665744179344840871450481)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_5_6 :
    pairMassBracketQuadraticQ 5 6 = pairMassBracketScalarDataQ3 2 5 6 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((141996298700341 : ℚ) / 16384000000000)⁻¹ ^ 2 =
    ((2315845044319893323776000000000000000000000000 : ℚ) / 182400692785911711400103076343673575289409035463)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_5_7 :
    pairMassBracketQuadraticQ 5 7 = pairMassBracketScalarDataQ3 2 5 7 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((26017390440279637 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((8469376162084181298380800000000000000000000000000 : ℚ) / 874786080663615440746601050973791686656958827354241)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_6_0 :
    pairMassBracketQuadraticQ 6 0 = pairMassBracketScalarDataQ3 2 6 0 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2699612110398741 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((2371425325383570763546624000000000000000000000000 : ℚ) / 65928799944184896866343696026637566870155821817863)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_6_1 :
    pairMassBracketQuadraticQ 6 1 = pairMassBracketScalarDataQ3 2 6 1 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((939723850454087 : ℚ) / 163840000000000)⁻¹ ^ 2 =
    ((231584504431989332377600000000000000000000000000 : ℚ) / 7988641539685261398264135270280739646044184771087)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_6_2 :
    pairMassBracketQuadraticQ 6 2 = pairMassBracketScalarDataQ3 2 6 2 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((3324009927466463 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((2371425325383570763546624000000000000000000000000 : ℚ) / 99953282159761707850252712160947824377666954287487)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_6_3 :
    pairMassBracketQuadraticQ 6 3 = pairMassBracketScalarDataQ3 2 6 3 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((458947296594237 : ℚ) / 65536000000000)⁻¹ ^ 2 =
    ((3368501882647117561856000000000000000000000000 : ℚ) / 173222930738219379845407151744612871861784851717)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_6_4 :
    pairMassBracketQuadraticQ 6 4 = pairMassBracketScalarDataQ3 2 6 4 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((20355535508151893 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((8469376162084181298380800000000000000000000000000 : ℚ) / 535475320649277232235894671253699036707702892869761)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_6_5 :
    pairMassBracketQuadraticQ 6 5 = pairMassBracketScalarDataQ3 2 6 5 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((141996298700341 : ℚ) / 16384000000000)⁻¹ ^ 2 =
    ((2315845044319893323776000000000000000000000000 : ℚ) / 182400692785911711400103076343673575289409035463)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_6_6 :
    pairMassBracketQuadraticQ 6 6 = pairMassBracketScalarDataQ3 2 6 6 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((25555935937052487 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((59285633134589269088665600000000000000000000000000 : ℚ) / 5908211271077123052170311618160418624988454285647887)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_6_7 :
    pairMassBracketQuadraticQ 6 7 = pairMassBracketScalarDataQ3 2 6 7 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((724288679118017 : ℚ) / 65536000000000)⁻¹ ^ 2 =
    ((37053520709118293180416000000000000000000000000 : ℚ) / 4745651358454399904295057717537007968861556291647)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_7_0 :
    pairMassBracketQuadraticQ 7 0 = pairMassBracketScalarDataQ3 2 7 0 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((16138212731273 : ℚ) / 2560000000000)⁻¹ ^ 2 =
    ((56539185652341145600000000000000000000000000 : ℚ) / 2356043513762555031965221240164247214238061167)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_7_1 :
    pairMassBracketQuadraticQ 7 1 = pairMassBracketScalarDataQ3 2 7 1 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((3608069385946389 : ℚ) / 524288000000000)⁻¹ ^ 2 =
    ((338775046483367251935232000000000000000000000000 : ℚ) / 16823802320726375619476458111174651415378592800769)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_7_2 :
    pairMassBracketQuadraticQ 7 2 = pairMassBracketScalarDataQ3 2 7 2 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((2456356390514579 : ℚ) / 327680000000000)⁻¹ ^ 2 =
    ((132334002532565332787200000000000000000000000000 : ℚ) / 7797531755305661874822811455034346867145867929649)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_7_3 :
    pairMassBracketQuadraticQ 7 3 = pairMassBracketScalarDataQ3 2 7 3 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((21453132832392731 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((59285633134589269088665600000000000000000000000000 : ℚ) / 4163455036810920689538714359313210595891255576323303)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_7_4 :
    pairMassBracketQuadraticQ 7 4 = pairMassBracketScalarDataQ3 2 7 4 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((36786378854649 : ℚ) / 4096000000000)⁻¹ ^ 2 =
    ((144740315269993332736000000000000000000000000 : ℚ) / 12241834777015285854934648227510695846941684623)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_7_5 :
    pairMassBracketQuadraticQ 7 5 = pairMassBracketScalarDataQ3 2 7 5 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((26017390440279637 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((8469376162084181298380800000000000000000000000000 : ℚ) / 874786080663615440746601050973791686656958827354241)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_7_6 :
    pairMassBracketQuadraticQ 7 6 = pairMassBracketScalarDataQ3 2 7 6 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((724288679118017 : ℚ) / 65536000000000)⁻¹ ^ 2 =
    ((37053520709118293180416000000000000000000000000 : ℚ) / 4745651358454399904295057717537007968861556291647)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_2_7_7 :
    pairMassBracketQuadraticQ 7 7 = pairMassBracketScalarDataQ3 2 7 7 := by
  simp only [pairMassBracketQuadraticQ, pairMassCellCenterQ_eq_data]
  change (pairMassChooseQ 2 - 3 * pairMassChooseQ 3) * ((32501843052713607 : ℚ) / 2621440000000000)⁻¹ ^ 2 =
    ((59285633134589269088665600000000000000000000000000 : ℚ) / 9556270026559664710514719166798729147424966956829327)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_0_0 :
    pairMassBracketCubicQ 0 0 = pairMassBracketScalarDataQ3 3 0 0 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((784751987730939 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 13115684563749049993824822051158396788274969525055675994021312311)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_0_1 :
    pairMassBracketCubicQ 0 1 = pairMassBracketScalarDataQ3 3 0 1 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((129399845653673 : ℚ) / 65536000000000)⁻¹ ^ 3 =
    ((-180478579343462287733161984000000000000000000000000000000000 : ℚ) / 58802388203751849796237158407135383557361289543765892978653973)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_0_2 :
    pairMassBracketCubicQ 0 2 = pairMassBracketScalarDataQ3 3 0 2 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((6384501536296597 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 7062763718603089609739471449687932964537250073319138344595612442937)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_0_3 :
    pairMassBracketCubicQ 0 3 = pairMassBracketScalarDataQ3 3 0 3 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((12008004010203 : ℚ) / 4096000000000)⁻¹ ^ 3 =
    ((-44062153160024972591104000000000000000000000000000000000 : ℚ) / 46990077659917232939830716119837870200284846198952620005463)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_0_4 :
    pairMassBracketCubicQ 0 4 = pairMassBracketScalarDataQ3 3 0 4 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((9213696414273083 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 21227330669318653155881217968096071844741399772225461108807243373303)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_0_5 :
    pairMassBracketCubicQ 0 5 = pairMassBracketScalarDataQ3 3 0 5 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((277651564423807 : ℚ) / 65536000000000)⁻¹ ^ 3 =
    ((-180478579343462287733161984000000000000000000000000000000000 : ℚ) / 580890219768120121560109140887935974458247960315380341847936067)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_0_6 :
    pairMassBracketCubicQ 0 6 = pairMassBracketScalarDataQ3 3 0 6 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2699612110398741 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 533946560260132161834080169531157229402894832653633915005219531449)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_0_7 :
    pairMassBracketCubicQ 0 7 = pairMassBracketScalarDataQ3 3 0 7 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((16138212731273 : ℚ) / 2560000000000)⁻¹ ^ 3 =
    ((-10757361611334221824000000000000000000000000000000000000 : ℚ) / 114066994287708117621619268672930304967238408038569323326773)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_1_0 :
    pairMassBracketCubicQ 1 0 = pairMassBracketScalarDataQ3 3 1 0 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((129399845653673 : ℚ) / 65536000000000)⁻¹ ^ 3 =
    ((-180478579343462287733161984000000000000000000000000000000000 : ℚ) / 58802388203751849796237158407135383557361289543765892978653973)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_1_1 :
    pairMassBracketCubicQ 1 1 = pairMassBracketScalarDataQ3 3 1 1 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((6480383081275047 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 7385769137853075735303445459830744847738220372562250379766357077787)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_1_2 :
    pairMassBracketCubicQ 1 2 = pairMassBracketScalarDataQ3 3 1 2 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((48445973674453 : ℚ) / 16384000000000)⁻¹ ^ 3 =
    ((-2819977802241598245830656000000000000000000000000000000000 : ℚ) / 3085792765306716995890085697993329426190193199187420103390713)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_1_3 :
    pairMassBracketCubicQ 1 3 = pairMassBracketScalarDataQ3 3 1 3 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((364625478797789 : ℚ) / 104857600000000)⁻¹ ^ 3 =
    ((-739240260990821530555031486464000000000000000000000000000000 : ℚ) / 1315632905623975707814305304034442788224453550375215750444291761)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_1_4 :
    pairMassBracketCubicQ 1 4 = pairMassBracketScalarDataQ3 3 1 4 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((1337493956407161 : ℚ) / 327680000000000)⁻¹ ^ 3 =
    ((-22559822417932785966645248000000000000000000000000000000000000 : ℚ) / 64933554170710614183952853987630499082385620175631386915569768389)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_1_5 :
    pairMassBracketCubicQ 1 5 = pairMassBracketScalarDataQ3 3 1 5 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((505240994229427 : ℚ) / 104857600000000)⁻¹ ^ 3 =
    ((-739240260990821530555031486464000000000000000000000000000000 : ℚ) / 3500172378149912316302845896762805407577613884192923264895515327)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_1_6 :
    pairMassBracketCubicQ 1 6 = pairMassBracketScalarDataQ3 3 1 6 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((939723850454087 : ℚ) / 163840000000000)⁻¹ ^ 3 =
    ((-2819977802241598245830656000000000000000000000000000000000000 : ℚ) / 22521350962711499700792653416987720900512746420551530165295747707)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_1_7 :
    pairMassBracketCubicQ 1 7 = pairMassBracketScalarDataQ3 3 1 7 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((3608069385946389 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 1274730368281159614072219974841402729380268606990880052803031435961)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_2_0 :
    pairMassBracketCubicQ 2 0 = pairMassBracketScalarDataQ3 3 2 0 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((6384501536296597 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 7062763718603089609739471449687932964537250073319138344595612442937)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_2_1 :
    pairMassBracketCubicQ 2 1 = pairMassBracketScalarDataQ3 3 2 1 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((48445973674453 : ℚ) / 16384000000000)⁻¹ ^ 3 =
    ((-2819977802241598245830656000000000000000000000000000000000 : ℚ) / 3085792765306716995890085697993329426190193199187420103390713)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_2_2 :
    pairMassBracketCubicQ 2 2 = pairMassBracketScalarDataQ3 3 2 2 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((9091899507783007 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 20396590209012106594284981483431813494853736678672609924162144941667)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_2_3 :
    pairMassBracketCubicQ 2 3 = pairMassBracketScalarDataQ3 3 2 3 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((1315948340535527 : ℚ) / 327680000000000)⁻¹ ^ 3 =
    ((-22559822417932785966645248000000000000000000000000000000000000 : ℚ) / 61845800078103743278988400916392563673472607497762200169393233627)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_2_4 :
    pairMassBracketCubicQ 2 4 = pairMassBracketScalarDataQ3 3 2 4 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2435974293158429 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 392294114523449426370660820741544431051504445991405193804035670641)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_2_5 :
    pairMassBracketCubicQ 2 5 = pairMassBracketScalarDataQ3 3 2 5 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((885637985042677 : ℚ) / 163840000000000)⁻¹ ^ 3 =
    ((-2819977802241598245830656000000000000000000000000000000000000 : ℚ) / 18852215497394991436118952333898995638180633128858890702229967577)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_2_6 :
    pairMassBracketCubicQ 2 6 = pairMassBracketScalarDataQ3 3 2 6 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((3324009927466463 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 996737106545713274114408310631849862499449274462424981143759145443)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_2_7 :
    pairMassBracketCubicQ 2 7 = pairMassBracketScalarDataQ3 3 2 7 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2456356390514579 : ℚ) / 327680000000000)⁻¹ ^ 3 =
    ((-22559822417932785966645248000000000000000000000000000000000000 : ℚ) / 402223856105093925892790329561688524938517411480407348790097908191)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_3_0 :
    pairMassBracketCubicQ 3 0 = pairMassBracketScalarDataQ3 3 3 0 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((12008004010203 : ℚ) / 4096000000000)⁻¹ ^ 3 =
    ((-44062153160024972591104000000000000000000000000000000000 : ℚ) / 46990077659917232939830716119837870200284846198952620005463)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_3_1 :
    pairMassBracketCubicQ 3 1 = pairMassBracketScalarDataQ3 3 3 1 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((364625478797789 : ℚ) / 104857600000000)⁻¹ ^ 3 =
    ((-739240260990821530555031486464000000000000000000000000000000 : ℚ) / 1315632905623975707814305304034442788224453550375215750444291761)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_3_2 :
    pairMassBracketCubicQ 3 2 = pairMassBracketScalarDataQ3 3 3 2 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((1315948340535527 : ℚ) / 327680000000000)⁻¹ ^ 3 =
    ((-22559822417932785966645248000000000000000000000000000000000000 : ℚ) / 61845800078103743278988400916392563673472607497762200169393233627)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_3_3 :
    pairMassBracketCubicQ 3 3 = pairMassBracketScalarDataQ3 3 3 3 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2407875892038483 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 378875031572925620292847348392065977415396442655446144231812137503)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_3_4 :
    pairMassBracketCubicQ 3 4 = pairMassBracketScalarDataQ3 3 3 4 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((26893403922487 : ℚ) / 5120000000000)⁻¹ ^ 3 =
    ((-86058892890673774592000000000000000000000000000000000000 : ℚ) / 527874902482814583974886579259432392429314182602301892144907)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_3_5 :
    pairMassBracketCubicQ 3 5 = pairMassBracketScalarDataQ3 3 3 5 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((633444975971641 : ℚ) / 104857600000000)⁻¹ ^ 3 =
    ((-739240260990821530555031486464000000000000000000000000000000 : ℚ) / 6897955334576421629825212413771526448849404685307375387955615749)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_3_6 :
    pairMassBracketCubicQ 3 6 = pairMassBracketScalarDataQ3 3 3 6 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((458947296594237 : ℚ) / 65536000000000)⁻¹ ^ 3 =
    ((-180478579343462287733161984000000000000000000000000000000000 : ℚ) / 2623506460424405916621814737803750001387797364671715221337912657)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_3_7 :
    pairMassBracketCubicQ 3 7 = pairMassBracketScalarDataQ3 3 3 7 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((21453132832392731 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 267957461839197747242858584950525936105277247449978506389187369331479)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_4_0 :
    pairMassBracketCubicQ 4 0 = pairMassBracketScalarDataQ3 3 4 0 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((9213696414273083 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 21227330669318653155881217968096071844741399772225461108807243373303)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_4_1 :
    pairMassBracketCubicQ 4 1 = pairMassBracketScalarDataQ3 3 4 1 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((1337493956407161 : ℚ) / 327680000000000)⁻¹ ^ 3 =
    ((-22559822417932785966645248000000000000000000000000000000000000 : ℚ) / 64933554170710614183952853987630499082385620175631386915569768389)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_4_2 :
    pairMassBracketCubicQ 4 2 = pairMassBracketScalarDataQ3 3 4 2 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2435974293158429 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 392294114523449426370660820741544431051504445991405193804035670641)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_4_3 :
    pairMassBracketCubicQ 4 3 = pairMassBracketScalarDataQ3 3 4 3 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((26893403922487 : ℚ) / 5120000000000)⁻¹ ^ 3 =
    ((-86058892890673774592000000000000000000000000000000000000 : ℚ) / 527874902482814583974886579259432392429314182602301892144907)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_4_4 :
    pairMassBracketCubicQ 4 4 = pairMassBracketScalarDataQ3 3 4 4 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((623382905170263 : ℚ) / 104857600000000)⁻¹ ^ 3 =
    ((-739240260990821530555031486464000000000000000000000000000000 : ℚ) / 6574433785302774215393125439327476460111220517460751233342340843)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_4_5 :
    pairMassBracketCubicQ 4 5 = pairMassBracketScalarDataQ3 3 4 5 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2217660984882191 : ℚ) / 327680000000000)⁻¹ ^ 3 =
    ((-22559822417932785966645248000000000000000000000000000000000000 : ℚ) / 295991444446402986483456770976588642797241069666031186884725730099)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_4_6 :
    pairMassBracketCubicQ 4 6 = pairMassBracketScalarDataQ3 3 4 6 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((20355535508151893 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 228897624967523048632055034469261951714345374974855046580085346759033)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_4_7 :
    pairMassBracketCubicQ 4 7 = pairMassBracketScalarDataQ3 3 4 7 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((36786378854649 : ℚ) / 4096000000000)⁻¹ ^ 3 =
    ((-44062153160024972591104000000000000000000000000000000000 : ℚ) / 1350998315949905602737048526884841888387246948173987946086981)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_5_0 :
    pairMassBracketCubicQ 5 0 = pairMassBracketScalarDataQ3 3 5 0 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((277651564423807 : ℚ) / 65536000000000)⁻¹ ^ 3 =
    ((-180478579343462287733161984000000000000000000000000000000000 : ℚ) / 580890219768120121560109140887935974458247960315380341847936067)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_5_1 :
    pairMassBracketCubicQ 5 1 = pairMassBracketScalarDataQ3 3 5 1 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((505240994229427 : ℚ) / 104857600000000)⁻¹ ^ 3 =
    ((-739240260990821530555031486464000000000000000000000000000000 : ℚ) / 3500172378149912316302845896762805407577613884192923264895515327)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_5_2 :
    pairMassBracketCubicQ 5 2 = pairMassBracketScalarDataQ3 3 5 2 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((885637985042677 : ℚ) / 163840000000000)⁻¹ ^ 3 =
    ((-2819977802241598245830656000000000000000000000000000000000000 : ℚ) / 18852215497394991436118952333898995638180633128858890702229967577)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_5_3 :
    pairMassBracketCubicQ 5 3 = pairMassBracketScalarDataQ3 3 5 3 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((633444975971641 : ℚ) / 104857600000000)⁻¹ ^ 3 =
    ((-739240260990821530555031486464000000000000000000000000000000 : ℚ) / 6897955334576421629825212413771526448849404685307375387955615749)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_5_4 :
    pairMassBracketCubicQ 5 4 = pairMassBracketScalarDataQ3 3 5 4 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2217660984882191 : ℚ) / 327680000000000)⁻¹ ^ 3 =
    ((-22559822417932785966645248000000000000000000000000000000000000 : ℚ) / 295991444446402986483456770976588642797241069666031186884725730099)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_5_5 :
    pairMassBracketCubicQ 5 5 = pairMassBracketScalarDataQ3 3 5 5 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((3999642261495923 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 1736429421754053399816061666680506667579485540959517613267435668223)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_5_6 :
    pairMassBracketCubicQ 5 6 = pairMassBracketScalarDataQ3 3 5 6 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((141996298700341 : ℚ) / 16384000000000)⁻¹ ^ 3 =
    ((-2819977802241598245830656000000000000000000000000000000000 : ℚ) / 77700669767932359480111682598617836003375171105770187837578649)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_5_7 :
    pairMassBracketCubicQ 5 7 = pairMassBracketScalarDataQ3 3 5 7 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((26017390440279637 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 477952671259292035362266257619174293738499281143392177931678855700857)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_6_0 :
    pairMassBracketCubicQ 6 0 = pairMassBracketScalarDataQ3 3 6 0 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2699612110398741 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 533946560260132161834080169531157229402894832653633915005219531449)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_6_1 :
    pairMassBracketCubicQ 6 1 = pairMassBracketScalarDataQ3 3 6 1 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((939723850454087 : ℚ) / 163840000000000)⁻¹ ^ 3 =
    ((-2819977802241598245830656000000000000000000000000000000000000 : ℚ) / 22521350962711499700792653416987720900512746420551530165295747707)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_6_2 :
    pairMassBracketCubicQ 6 2 = pairMassBracketScalarDataQ3 3 6 2 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((3324009927466463 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 996737106545713274114408310631849862499449274462424981143759145443)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_6_3 :
    pairMassBracketCubicQ 6 3 = pairMassBracketScalarDataQ3 3 6 3 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((458947296594237 : ℚ) / 65536000000000)⁻¹ ^ 3 =
    ((-180478579343462287733161984000000000000000000000000000000000 : ℚ) / 2623506460424405916621814737803750001387797364671715221337912657)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_6_4 :
    pairMassBracketCubicQ 6 4 = pairMassBracketScalarDataQ3 3 6 4 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((20355535508151893 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 228897624967523048632055034469261951714345374974855046580085346759033)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_6_5 :
    pairMassBracketCubicQ 6 5 = pairMassBracketScalarDataQ3 3 6 5 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((141996298700341 : ℚ) / 16384000000000)⁻¹ ^ 3 =
    ((-2819977802241598245830656000000000000000000000000000000000 : ℚ) / 77700669767932359480111682598617836003375171105770187837578649)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_6_6 :
    pairMassBracketCubicQ 6 6 = pairMassBracketScalarDataQ3 3 6 6 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((25555935937052487 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 452969606238655205977546252454021181945626852943120803134517758934907)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_6_7 :
    pairMassBracketCubicQ 6 7 = pairMassBracketScalarDataQ3 3 6 7 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((724288679118017 : ℚ) / 65536000000000)⁻¹ ^ 3 =
    ((-180478579343462287733161984000000000000000000000000000000000 : ℚ) / 10311664661908680974370920081906473386089324429466835959552911997)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_7_0 :
    pairMassBracketCubicQ 7 0 = pairMassBracketScalarDataQ3 3 7 0 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((16138212731273 : ℚ) / 2560000000000)⁻¹ ^ 3 =
    ((-10757361611334221824000000000000000000000000000000000000 : ℚ) / 114066994287708117621619268672930304967238408038569323326773)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_7_1 :
    pairMassBracketCubicQ 7 1 = pairMassBracketScalarDataQ3 3 7 1 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((3608069385946389 : ℚ) / 524288000000000)⁻¹ ^ 3 =
    ((-92405032623852691319378935808000000000000000000000000000000000 : ℚ) / 1274730368281159614072219974841402729380268606990880052803031435961)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_7_2 :
    pairMassBracketCubicQ 7 2 = pairMassBracketScalarDataQ3 3 7 2 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((2456356390514579 : ℚ) / 327680000000000)⁻¹ ^ 3 =
    ((-22559822417932785966645248000000000000000000000000000000000000 : ℚ) / 402223856105093925892790329561688524938517411480407348790097908191)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_7_3 :
    pairMassBracketCubicQ 7 3 = pairMassBracketScalarDataQ3 3 7 3 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((21453132832392731 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 267957461839197747242858584950525936105277247449978506389187369331479)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_7_4 :
    pairMassBracketCubicQ 7 4 = pairMassBracketScalarDataQ3 3 7 4 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((36786378854649 : ℚ) / 4096000000000)⁻¹ ^ 3 =
    ((-44062153160024972591104000000000000000000000000000000000 : ℚ) / 1350998315949905602737048526884841888387246948173987946086981)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_7_5 :
    pairMassBracketCubicQ 7 5 = pairMassBracketScalarDataQ3 3 7 5 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((26017390440279637 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 477952671259292035362266257619174293738499281143392177931678855700857)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_7_6 :
    pairMassBracketCubicQ 7 6 = pairMassBracketScalarDataQ3 3 7 6 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((724288679118017 : ℚ) / 65536000000000)⁻¹ ^ 3 =
    ((-180478579343462287733161984000000000000000000000000000000000 : ℚ) / 10311664661908680974370920081906473386089324429466835959552911997)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketScalarCase_3_7_7 :
    pairMassBracketCubicQ 7 7 = pairMassBracketScalarDataQ3 3 7 7 := by
  simp only [pairMassBracketCubicQ, pairMassCellCenterQ_eq_data]
  change pairMassChooseQ 3 * ((32501843052713607 : ℚ) / 2621440000000000)⁻¹ ^ 3 =
    ((-11550629077981586414922366976000000000000000000000000000000000000 : ℚ) / 931789165717780545359206737450674343669377360063578002299844328657467)
  norm_num [pairMassChooseQ, pairMassPQ]

private theorem pairMassBracketConstantCases_eq_data (i j : Fin 8) :
    pairMassBracketConstantQ i j = pairMassBracketScalarDataQ3 0 i j := by
  fin_cases i <;> fin_cases j
  · exact pairMassBracketScalarCase_0_0_0
  · exact pairMassBracketScalarCase_0_0_1
  · exact pairMassBracketScalarCase_0_0_2
  · exact pairMassBracketScalarCase_0_0_3
  · exact pairMassBracketScalarCase_0_0_4
  · exact pairMassBracketScalarCase_0_0_5
  · exact pairMassBracketScalarCase_0_0_6
  · exact pairMassBracketScalarCase_0_0_7
  · exact pairMassBracketScalarCase_0_1_0
  · exact pairMassBracketScalarCase_0_1_1
  · exact pairMassBracketScalarCase_0_1_2
  · exact pairMassBracketScalarCase_0_1_3
  · exact pairMassBracketScalarCase_0_1_4
  · exact pairMassBracketScalarCase_0_1_5
  · exact pairMassBracketScalarCase_0_1_6
  · exact pairMassBracketScalarCase_0_1_7
  · exact pairMassBracketScalarCase_0_2_0
  · exact pairMassBracketScalarCase_0_2_1
  · exact pairMassBracketScalarCase_0_2_2
  · exact pairMassBracketScalarCase_0_2_3
  · exact pairMassBracketScalarCase_0_2_4
  · exact pairMassBracketScalarCase_0_2_5
  · exact pairMassBracketScalarCase_0_2_6
  · exact pairMassBracketScalarCase_0_2_7
  · exact pairMassBracketScalarCase_0_3_0
  · exact pairMassBracketScalarCase_0_3_1
  · exact pairMassBracketScalarCase_0_3_2
  · exact pairMassBracketScalarCase_0_3_3
  · exact pairMassBracketScalarCase_0_3_4
  · exact pairMassBracketScalarCase_0_3_5
  · exact pairMassBracketScalarCase_0_3_6
  · exact pairMassBracketScalarCase_0_3_7
  · exact pairMassBracketScalarCase_0_4_0
  · exact pairMassBracketScalarCase_0_4_1
  · exact pairMassBracketScalarCase_0_4_2
  · exact pairMassBracketScalarCase_0_4_3
  · exact pairMassBracketScalarCase_0_4_4
  · exact pairMassBracketScalarCase_0_4_5
  · exact pairMassBracketScalarCase_0_4_6
  · exact pairMassBracketScalarCase_0_4_7
  · exact pairMassBracketScalarCase_0_5_0
  · exact pairMassBracketScalarCase_0_5_1
  · exact pairMassBracketScalarCase_0_5_2
  · exact pairMassBracketScalarCase_0_5_3
  · exact pairMassBracketScalarCase_0_5_4
  · exact pairMassBracketScalarCase_0_5_5
  · exact pairMassBracketScalarCase_0_5_6
  · exact pairMassBracketScalarCase_0_5_7
  · exact pairMassBracketScalarCase_0_6_0
  · exact pairMassBracketScalarCase_0_6_1
  · exact pairMassBracketScalarCase_0_6_2
  · exact pairMassBracketScalarCase_0_6_3
  · exact pairMassBracketScalarCase_0_6_4
  · exact pairMassBracketScalarCase_0_6_5
  · exact pairMassBracketScalarCase_0_6_6
  · exact pairMassBracketScalarCase_0_6_7
  · exact pairMassBracketScalarCase_0_7_0
  · exact pairMassBracketScalarCase_0_7_1
  · exact pairMassBracketScalarCase_0_7_2
  · exact pairMassBracketScalarCase_0_7_3
  · exact pairMassBracketScalarCase_0_7_4
  · exact pairMassBracketScalarCase_0_7_5
  · exact pairMassBracketScalarCase_0_7_6
  · exact pairMassBracketScalarCase_0_7_7

private theorem pairMassBracketLinearCases_eq_data (i j : Fin 8) :
    pairMassBracketLinearQ i j = pairMassBracketScalarDataQ3 1 i j := by
  fin_cases i <;> fin_cases j
  · exact pairMassBracketScalarCase_1_0_0
  · exact pairMassBracketScalarCase_1_0_1
  · exact pairMassBracketScalarCase_1_0_2
  · exact pairMassBracketScalarCase_1_0_3
  · exact pairMassBracketScalarCase_1_0_4
  · exact pairMassBracketScalarCase_1_0_5
  · exact pairMassBracketScalarCase_1_0_6
  · exact pairMassBracketScalarCase_1_0_7
  · exact pairMassBracketScalarCase_1_1_0
  · exact pairMassBracketScalarCase_1_1_1
  · exact pairMassBracketScalarCase_1_1_2
  · exact pairMassBracketScalarCase_1_1_3
  · exact pairMassBracketScalarCase_1_1_4
  · exact pairMassBracketScalarCase_1_1_5
  · exact pairMassBracketScalarCase_1_1_6
  · exact pairMassBracketScalarCase_1_1_7
  · exact pairMassBracketScalarCase_1_2_0
  · exact pairMassBracketScalarCase_1_2_1
  · exact pairMassBracketScalarCase_1_2_2
  · exact pairMassBracketScalarCase_1_2_3
  · exact pairMassBracketScalarCase_1_2_4
  · exact pairMassBracketScalarCase_1_2_5
  · exact pairMassBracketScalarCase_1_2_6
  · exact pairMassBracketScalarCase_1_2_7
  · exact pairMassBracketScalarCase_1_3_0
  · exact pairMassBracketScalarCase_1_3_1
  · exact pairMassBracketScalarCase_1_3_2
  · exact pairMassBracketScalarCase_1_3_3
  · exact pairMassBracketScalarCase_1_3_4
  · exact pairMassBracketScalarCase_1_3_5
  · exact pairMassBracketScalarCase_1_3_6
  · exact pairMassBracketScalarCase_1_3_7
  · exact pairMassBracketScalarCase_1_4_0
  · exact pairMassBracketScalarCase_1_4_1
  · exact pairMassBracketScalarCase_1_4_2
  · exact pairMassBracketScalarCase_1_4_3
  · exact pairMassBracketScalarCase_1_4_4
  · exact pairMassBracketScalarCase_1_4_5
  · exact pairMassBracketScalarCase_1_4_6
  · exact pairMassBracketScalarCase_1_4_7
  · exact pairMassBracketScalarCase_1_5_0
  · exact pairMassBracketScalarCase_1_5_1
  · exact pairMassBracketScalarCase_1_5_2
  · exact pairMassBracketScalarCase_1_5_3
  · exact pairMassBracketScalarCase_1_5_4
  · exact pairMassBracketScalarCase_1_5_5
  · exact pairMassBracketScalarCase_1_5_6
  · exact pairMassBracketScalarCase_1_5_7
  · exact pairMassBracketScalarCase_1_6_0
  · exact pairMassBracketScalarCase_1_6_1
  · exact pairMassBracketScalarCase_1_6_2
  · exact pairMassBracketScalarCase_1_6_3
  · exact pairMassBracketScalarCase_1_6_4
  · exact pairMassBracketScalarCase_1_6_5
  · exact pairMassBracketScalarCase_1_6_6
  · exact pairMassBracketScalarCase_1_6_7
  · exact pairMassBracketScalarCase_1_7_0
  · exact pairMassBracketScalarCase_1_7_1
  · exact pairMassBracketScalarCase_1_7_2
  · exact pairMassBracketScalarCase_1_7_3
  · exact pairMassBracketScalarCase_1_7_4
  · exact pairMassBracketScalarCase_1_7_5
  · exact pairMassBracketScalarCase_1_7_6
  · exact pairMassBracketScalarCase_1_7_7

private theorem pairMassBracketQuadraticCases_eq_data (i j : Fin 8) :
    pairMassBracketQuadraticQ i j = pairMassBracketScalarDataQ3 2 i j := by
  fin_cases i <;> fin_cases j
  · exact pairMassBracketScalarCase_2_0_0
  · exact pairMassBracketScalarCase_2_0_1
  · exact pairMassBracketScalarCase_2_0_2
  · exact pairMassBracketScalarCase_2_0_3
  · exact pairMassBracketScalarCase_2_0_4
  · exact pairMassBracketScalarCase_2_0_5
  · exact pairMassBracketScalarCase_2_0_6
  · exact pairMassBracketScalarCase_2_0_7
  · exact pairMassBracketScalarCase_2_1_0
  · exact pairMassBracketScalarCase_2_1_1
  · exact pairMassBracketScalarCase_2_1_2
  · exact pairMassBracketScalarCase_2_1_3
  · exact pairMassBracketScalarCase_2_1_4
  · exact pairMassBracketScalarCase_2_1_5
  · exact pairMassBracketScalarCase_2_1_6
  · exact pairMassBracketScalarCase_2_1_7
  · exact pairMassBracketScalarCase_2_2_0
  · exact pairMassBracketScalarCase_2_2_1
  · exact pairMassBracketScalarCase_2_2_2
  · exact pairMassBracketScalarCase_2_2_3
  · exact pairMassBracketScalarCase_2_2_4
  · exact pairMassBracketScalarCase_2_2_5
  · exact pairMassBracketScalarCase_2_2_6
  · exact pairMassBracketScalarCase_2_2_7
  · exact pairMassBracketScalarCase_2_3_0
  · exact pairMassBracketScalarCase_2_3_1
  · exact pairMassBracketScalarCase_2_3_2
  · exact pairMassBracketScalarCase_2_3_3
  · exact pairMassBracketScalarCase_2_3_4
  · exact pairMassBracketScalarCase_2_3_5
  · exact pairMassBracketScalarCase_2_3_6
  · exact pairMassBracketScalarCase_2_3_7
  · exact pairMassBracketScalarCase_2_4_0
  · exact pairMassBracketScalarCase_2_4_1
  · exact pairMassBracketScalarCase_2_4_2
  · exact pairMassBracketScalarCase_2_4_3
  · exact pairMassBracketScalarCase_2_4_4
  · exact pairMassBracketScalarCase_2_4_5
  · exact pairMassBracketScalarCase_2_4_6
  · exact pairMassBracketScalarCase_2_4_7
  · exact pairMassBracketScalarCase_2_5_0
  · exact pairMassBracketScalarCase_2_5_1
  · exact pairMassBracketScalarCase_2_5_2
  · exact pairMassBracketScalarCase_2_5_3
  · exact pairMassBracketScalarCase_2_5_4
  · exact pairMassBracketScalarCase_2_5_5
  · exact pairMassBracketScalarCase_2_5_6
  · exact pairMassBracketScalarCase_2_5_7
  · exact pairMassBracketScalarCase_2_6_0
  · exact pairMassBracketScalarCase_2_6_1
  · exact pairMassBracketScalarCase_2_6_2
  · exact pairMassBracketScalarCase_2_6_3
  · exact pairMassBracketScalarCase_2_6_4
  · exact pairMassBracketScalarCase_2_6_5
  · exact pairMassBracketScalarCase_2_6_6
  · exact pairMassBracketScalarCase_2_6_7
  · exact pairMassBracketScalarCase_2_7_0
  · exact pairMassBracketScalarCase_2_7_1
  · exact pairMassBracketScalarCase_2_7_2
  · exact pairMassBracketScalarCase_2_7_3
  · exact pairMassBracketScalarCase_2_7_4
  · exact pairMassBracketScalarCase_2_7_5
  · exact pairMassBracketScalarCase_2_7_6
  · exact pairMassBracketScalarCase_2_7_7

private theorem pairMassBracketCubicCases_eq_data (i j : Fin 8) :
    pairMassBracketCubicQ i j = pairMassBracketScalarDataQ3 3 i j := by
  fin_cases i <;> fin_cases j
  · exact pairMassBracketScalarCase_3_0_0
  · exact pairMassBracketScalarCase_3_0_1
  · exact pairMassBracketScalarCase_3_0_2
  · exact pairMassBracketScalarCase_3_0_3
  · exact pairMassBracketScalarCase_3_0_4
  · exact pairMassBracketScalarCase_3_0_5
  · exact pairMassBracketScalarCase_3_0_6
  · exact pairMassBracketScalarCase_3_0_7
  · exact pairMassBracketScalarCase_3_1_0
  · exact pairMassBracketScalarCase_3_1_1
  · exact pairMassBracketScalarCase_3_1_2
  · exact pairMassBracketScalarCase_3_1_3
  · exact pairMassBracketScalarCase_3_1_4
  · exact pairMassBracketScalarCase_3_1_5
  · exact pairMassBracketScalarCase_3_1_6
  · exact pairMassBracketScalarCase_3_1_7
  · exact pairMassBracketScalarCase_3_2_0
  · exact pairMassBracketScalarCase_3_2_1
  · exact pairMassBracketScalarCase_3_2_2
  · exact pairMassBracketScalarCase_3_2_3
  · exact pairMassBracketScalarCase_3_2_4
  · exact pairMassBracketScalarCase_3_2_5
  · exact pairMassBracketScalarCase_3_2_6
  · exact pairMassBracketScalarCase_3_2_7
  · exact pairMassBracketScalarCase_3_3_0
  · exact pairMassBracketScalarCase_3_3_1
  · exact pairMassBracketScalarCase_3_3_2
  · exact pairMassBracketScalarCase_3_3_3
  · exact pairMassBracketScalarCase_3_3_4
  · exact pairMassBracketScalarCase_3_3_5
  · exact pairMassBracketScalarCase_3_3_6
  · exact pairMassBracketScalarCase_3_3_7
  · exact pairMassBracketScalarCase_3_4_0
  · exact pairMassBracketScalarCase_3_4_1
  · exact pairMassBracketScalarCase_3_4_2
  · exact pairMassBracketScalarCase_3_4_3
  · exact pairMassBracketScalarCase_3_4_4
  · exact pairMassBracketScalarCase_3_4_5
  · exact pairMassBracketScalarCase_3_4_6
  · exact pairMassBracketScalarCase_3_4_7
  · exact pairMassBracketScalarCase_3_5_0
  · exact pairMassBracketScalarCase_3_5_1
  · exact pairMassBracketScalarCase_3_5_2
  · exact pairMassBracketScalarCase_3_5_3
  · exact pairMassBracketScalarCase_3_5_4
  · exact pairMassBracketScalarCase_3_5_5
  · exact pairMassBracketScalarCase_3_5_6
  · exact pairMassBracketScalarCase_3_5_7
  · exact pairMassBracketScalarCase_3_6_0
  · exact pairMassBracketScalarCase_3_6_1
  · exact pairMassBracketScalarCase_3_6_2
  · exact pairMassBracketScalarCase_3_6_3
  · exact pairMassBracketScalarCase_3_6_4
  · exact pairMassBracketScalarCase_3_6_5
  · exact pairMassBracketScalarCase_3_6_6
  · exact pairMassBracketScalarCase_3_6_7
  · exact pairMassBracketScalarCase_3_7_0
  · exact pairMassBracketScalarCase_3_7_1
  · exact pairMassBracketScalarCase_3_7_2
  · exact pairMassBracketScalarCase_3_7_3
  · exact pairMassBracketScalarCase_3_7_4
  · exact pairMassBracketScalarCase_3_7_5
  · exact pairMassBracketScalarCase_3_7_6
  · exact pairMassBracketScalarCase_3_7_7

theorem pairMassBracketScalarsQ_eq_data (i j : Fin 8) :
    #v[pairMassBracketConstantQ i j, pairMassBracketLinearQ i j,
      pairMassBracketQuadraticQ i j, pairMassBracketCubicQ i j] =
    Vector.ofFn fun r => pairMassBracketScalarDataQ3 r i j := by
  apply Vector.ext
  intro r hr
  simp only [Vector.getElem_ofFn]
  interval_cases r
  · change pairMassBracketConstantQ i j = pairMassBracketScalarDataQ3 0 i j
    exact pairMassBracketConstantCases_eq_data i j
  · change pairMassBracketLinearQ i j = pairMassBracketScalarDataQ3 1 i j
    exact pairMassBracketLinearCases_eq_data i j
  · change pairMassBracketQuadraticQ i j = pairMassBracketScalarDataQ3 2 i j
    exact pairMassBracketQuadraticCases_eq_data i j
  · change pairMassBracketCubicQ i j = pairMassBracketScalarDataQ3 3 i j
    exact pairMassBracketCubicCases_eq_data i j

end

def pairMassDenseBracket3 (i j : Fin 8) : PairMassDense3 :=
  pairMassDenseAdd
    (pairMassDenseAdd
      (pairMassDenseScale (pairMassBracketConstantQ i j) pairMassDenseOne)
      (pairMassDenseScale (pairMassBracketLinearQ i j) pairMassDenseBase))
    (pairMassDenseAdd
      (pairMassDenseScale (pairMassBracketQuadraticQ i j) pairMassDenseBaseSquare)
      (pairMassDenseScale (pairMassBracketCubicQ i j) pairMassDenseBaseCube))

def pairMassMomentCoefficientQ (i : Fin 8) (n : ℕ) (s : Fin 2) : ℚ :=
  if s = 0 then -(6 / (6 + 5 * n)) * ((i : ℕ) / 8) ^ n
  else (6 / (6 + 5 * n)) * (((i : ℕ) + 1) / 8) ^ n

def pairMassDensePowerContraction3 (A : PairMassDense3)
    (i j : Fin 8) (s t : Fin 2) : ℚ :=
    ∑ a ∈ Finset.range 10, ∑ b ∈ Finset.range 10,
      pairMassDenseGet A a b * pairMassMomentCoefficientQ i a s *
        pairMassMomentCoefficientQ j b t

def pairMassPowerMatrixData3 (r : Fin 4) : PairMassDense3 :=
  match r with
  | ⟨0, _⟩ => pairMassDenseOne
  | ⟨1, _⟩ => pairMassDenseBase
  | ⟨2, _⟩ => pairMassDenseBaseSquareData
  | ⟨3, _⟩ => pairMassDenseBaseCubeData

def pairMassPowerInnerQ3 (r : Fin 4) (j : Fin 8) (t : Fin 2) (a : Fin 10) : ℚ :=
  ∑ b ∈ Finset.range 10,
    pairMassDenseGet (pairMassPowerMatrixData3 r) a b *
      pairMassMomentCoefficientQ j b t

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
theorem pairMassPowerInnerQ3_eq_data (r : Fin 4) (j : Fin 8) (t : Fin 2) :
    Vector.ofFn (pairMassPowerInnerQ3 r j t) =
      Vector.ofFn (pairMassPowerInnerData3 r j t) := by
  fin_cases r <;> fin_cases j <;> fin_cases t <;> decide +kernel

def pairMassStagedPowerContractionQ3
    (r : Fin 4) (i j : Fin 8) (s t : Fin 2) : ℚ :=
  ∑ a ∈ Finset.range 10,
    pairMassMomentCoefficientQ i a s *
      (if ha : a < 10 then pairMassPowerInnerData3 r j t ⟨a, ha⟩ else 0)

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
theorem pairMassStagedPowerContractionQ3_eq_data
    (r : Fin 4) (i j : Fin 8) (s : Fin 2) :
    Vector.ofFn (pairMassStagedPowerContractionQ3 r i j s) =
      Vector.ofFn (pairMassPowerContractionData3 r i j s) := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> fin_cases s <;> decide +kernel

def pairMassDenseCellCoefficients3 (i j : Fin 8) : Vector (Vector ℚ 2) 2 :=
  Vector.ofFn fun s => Vector.ofFn fun t =>
    pairMassBracketScalarDataQ3 ⟨0, by decide⟩ i j *
        pairMassPowerContractionData3 ⟨0, by decide⟩ i j s t +
      pairMassBracketScalarDataQ3 ⟨1, by decide⟩ i j *
        pairMassPowerContractionData3 ⟨1, by decide⟩ i j s t +
      pairMassBracketScalarDataQ3 ⟨2, by decide⟩ i j *
        pairMassPowerContractionData3 ⟨2, by decide⟩ i j s t +
      pairMassBracketScalarDataQ3 ⟨3, by decide⟩ i j *
        pairMassPowerContractionData3 ⟨3, by decide⟩ i j s t

def pairMassDenseCoefficientTable3 :
    Vector (Vector (Vector (Vector ℚ 2) 2) 8) 8 :=
  Vector.ofFn fun i => Vector.ofFn fun j => pairMassDenseCellCoefficients3 i j

def pairMassDeclaredCoefficientTable3 :
    Vector (Vector (Vector (Vector ℚ 2) 2) 8) 8 :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    Vector.ofFn fun s => Vector.ofFn fun t => pairMassContractionCoefficient3 i j s t

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
set_option backward.isDefEq.respectTransparency false in
theorem pairMassDenseCellCoefficients3_eq_declared (i j : Fin 8) :
    pairMassDenseCellCoefficients3 i j =
      Vector.ofFn fun s => Vector.ofFn fun t =>
        pairMassContractionCoefficient3 i j s t := by
  apply Vector.ext
  intro s hs
  apply Vector.ext
  intro t ht
  simp only [pairMassDenseCellCoefficients3, Vector.getElem_ofFn]
  convert! pairMassScalarCoefficients3_eq_declared i j ⟨s, hs⟩ ⟨t, ht⟩ using 1

end UnitDistance.Witness
