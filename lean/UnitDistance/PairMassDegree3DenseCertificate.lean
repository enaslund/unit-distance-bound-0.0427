module

public import UnitDistance.PairMassDegree3DenseRepresentationCertificate

@[expose] public section
set_option backward.privateInPublic true


open scoped BigOperators

namespace UnitDistance.Witness

noncomputable section

def pairMassRatPolynomialMap : Polynomial ℚ →+* Polynomial ℝ :=
  Polynomial.mapRingHom (Rat.castHom ℝ)

def pairMassRatNestedMap :
    Polynomial (Polynomial ℚ) →+* Polynomial (Polynomial ℝ) :=
  Polynomial.mapRingHom pairMassRatPolynomialMap

set_option maxHeartbeats 10000000 in
theorem pairMassRatNestedMap_base :
    pairMassRatNestedMap pairMassNestedPolynomialQ = pairNestedPolynomial := by
  unfold pairMassNestedPolynomialQ pairNestedPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_pow]
  change Polynomial.map pairMassRatPolynomialMap
      (Polynomial.C (∑ j : Fin 4,
        Polynomial.C (pairPowerCoefficients i j) * Polynomial.X ^ (j : ℕ))) *
      (Polynomial.map pairMassRatPolynomialMap Polynomial.X) ^ (i : ℕ) = _
  rw [Polynomial.map_C, Polynomial.map_X]
  congr 1
  rw [map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [pairMassRatPolynomialMap]

theorem pairMassRatNestedMap_coeff
    (P : Polynomial (Polynomial ℚ)) (a b : ℕ) :
    nestedCoeff (pairMassRatNestedMap P) a b =
      (pairMassNestedCoeffQ P a b : ℝ) := by
  simp [nestedCoeff, pairMassNestedCoeffQ, pairMassRatNestedMap,
    pairMassRatPolynomialMap, Polynomial.coeff_map]

set_option maxHeartbeats 10000000 in
theorem pairMassPolynomialQ_cast (t u : ℚ) :
    (pairMassPolynomialQ t u : ℝ) = polynomial (t : ℝ) (u : ℝ) := by
  norm_num [pairMassPolynomialQ, polynomial, bernstein3, pairPowerCoefficients,
    bernsteinCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem pairMassPQ_cast : (pairMassPQ : ℝ) = p := by
  norm_num [pairMassPQ, p, increment]

theorem pairMassChooseQ_cast (k : ℕ) :
    (pairMassChooseQ k : ℝ) = Ring.choose p k := by
  induction k with
  | zero => simp [pairMassChooseQ]
  | succ k ih =>
      rw [generalizedChoose_succ]
      simp only [pairMassChooseQ, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
        Rat.cast_natCast, ih, pairMassPQ_cast]
      norm_num [Nat.cast_add, Nat.cast_one]

theorem pairMassCellCenterQ_cast (i j : Fin 8) :
    (pairMassCellCenterQ i j : ℝ) = pairMassCellCenter i j := by
  unfold pairMassCellCenterQ pairMassCellCenter pairMassCellLower pairMassCellUpper
  push_cast
  rw [pairMassPolynomialQ_cast, pairMassPolynomialQ_cast]
  norm_num

theorem pairMassCellRadiusQ_cast (i j : Fin 8) :
    (pairMassCellRadiusQ i j : ℝ) = pairMassCellRadius i j := by
  unfold pairMassCellRadiusQ pairMassCellRadius pairMassCellLower pairMassCellUpper
  push_cast
  rw [pairMassPolynomialQ_cast, pairMassPolynomialQ_cast]
  norm_num

theorem pairMassTailQ_cast (i j : Fin 8) :
    (pairMassTailQ i j : ℝ) = pairCellTail (pairMassCellRadius i j) 3 := by
  unfold pairMassTailQ pairCellTail
  push_cast
  rw [pairMassChooseQ_cast, pairMassCellRadiusQ_cast]

theorem pairMassRatNestedMap_centered (i j : Fin 8) :
    pairMassRatNestedMap (pairMassCenteredPolynomialQ i j) =
      centeredPairPolynomial (pairMassCellCenter i j) := by
  unfold pairMassCenteredPolynomialQ centeredPairPolynomial
  simp only [map_add, map_mul, map_one]
  rw [pairMassRatNestedMap_base]
  simp [pairMassRatNestedMap, pairMassRatPolynomialMap,
    pairMassCellCenterQ_cast]
  ring

theorem pairMassRatNestedMap_bracket (i j : Fin 8) :
    pairMassRatNestedMap (pairMassBracketPolynomialQ i j) =
      pairMassCellBracket3 i j := by
  unfold pairMassBracketPolynomialQ pairMassCellBracket3
    pairCellBracketPolynomial pairBinomialPolynomial
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [map_add, map_mul, map_pow, map_one]
  simp only [pairMassRatNestedMap_centered]
  simp [pairMassRatNestedMap, pairMassRatPolynomialMap,
    pairMassChooseQ_cast, pairMassTailQ_cast]
  ring

theorem pairMassCellBracket3_coeff_eq_cast (i j : Fin 8) (a b : ℕ) :
    nestedCoeff (pairMassCellBracket3 i j) a b =
      (pairMassNestedCoeffQ (pairMassBracketPolynomialQ i j) a b : ℝ) := by
  rw [← pairMassRatNestedMap_bracket]
  exact pairMassRatNestedMap_coeff _ _ _

theorem pairMassRationalMoment_eq_endpoint_sum (i : Fin 8) (n : ℕ) :
    pairMassRationalMoment i n =
      ∑ s : Fin 2, (pairMassMomentCoefficientQ i n s : ℝ) *
        pairMassEndpointRoot ((i : ℕ) + (s : ℕ)) := by
  rw [Fin.sum_univ_two]
  norm_num [pairMassMomentCoefficientQ, pairMassRationalMoment]
  ring

def pairMassQContractionCoefficient3
    (i j : Fin 8) (s t : Fin 2) : ℚ :=
  ∑ a ∈ Finset.range 10, ∑ b ∈ Finset.range 10,
    pairMassNestedCoeffQ (pairMassBracketPolynomialQ i j) a b *
      pairMassMomentCoefficientQ i a s * pairMassMomentCoefficientQ j b t

theorem pairMassQContractionCoefficient3_eq_declared
    (i j : Fin 8) (s t : Fin 2) :
    pairMassQContractionCoefficient3 i j s t =
      pairMassContractionCoefficient3 i j s t := by
  rw [← pairMassDenseBracket3_contraction_eq_declared i j s t]
  unfold pairMassQContractionCoefficient3 pairMassDensePowerContraction3
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← pairMassDenseBracket3_rep i j a b
    (by simp only [Finset.mem_range] at ha; omega)
    (by simp only [Finset.mem_range] at hb; omega)]

theorem pairMassQContractionCoefficient3_cast
    (i j : Fin 8) (s t : Fin 2) :
    (pairMassQContractionCoefficient3 i j s t : ℝ) =
      ∑ a ∈ Finset.range 10, ∑ b ∈ Finset.range 10,
        (pairMassNestedCoeffQ (pairMassBracketPolynomialQ i j) a b : ℝ) *
          (pairMassMomentCoefficientQ i a s : ℝ) *
          (pairMassMomentCoefficientQ j b t : ℝ) := by
  simp [pairMassQContractionCoefficient3]

theorem pairMass_sum4_reorder
    (f : ℕ → ℕ → Fin 2 → Fin 2 → ℝ) :
    (∑ a ∈ Finset.range 10, ∑ b ∈ Finset.range 10,
      ∑ s : Fin 2, ∑ t : Fin 2, f a b s t) =
      ∑ s : Fin 2, ∑ t : Fin 2, ∑ a ∈ Finset.range 10,
        ∑ b ∈ Finset.range 10, f a b s t := by
  calc
    _ = ∑ a ∈ Finset.range 10, ∑ s : Fin 2,
          ∑ b ∈ Finset.range 10, ∑ t : Fin 2, f a b s t := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
    _ = ∑ s : Fin 2, ∑ a ∈ Finset.range 10,
          ∑ b ∈ Finset.range 10, ∑ t : Fin 2, f a b s t := by
        rw [Finset.sum_comm]
    _ = ∑ s : Fin 2, ∑ a ∈ Finset.range 10,
          ∑ t : Fin 2, ∑ b ∈ Finset.range 10, f a b s t := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_comm]

theorem pairMassCellContraction3_expansion (i j : Fin 8) :
    pairMassCellContraction3 i j =
      ∑ s : Fin 2, ∑ t : Fin 2,
        (pairMassContractionCoefficient3 i j s t : ℝ) *
          pairMassEndpointRoot ((i : ℕ) + (s : ℕ)) *
          pairMassEndpointRoot ((j : ℕ) + (t : ℕ)) := by
  rw [pairMassCellContraction3_eq_rangeRational]
  unfold pairMassCellRangeRationalContraction3 pairNestedRectangleSupport
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [← pairMassQContractionCoefficient3_eq_declared]
  simp_rw [pairMassQContractionCoefficient3_cast]
  simp_rw [pairMassCellBracket3_coeff_eq_cast,
    pairMassRationalMoment_eq_endpoint_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [pairMass_sum4_reorder, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end

end UnitDistance.Witness
