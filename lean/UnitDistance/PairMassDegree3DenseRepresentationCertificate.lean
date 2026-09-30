module

public import UnitDistance.PairMassDegree3DenseComputationCertificate

@[expose] public section
set_option backward.privateInPublic true


open scoped BigOperators

namespace UnitDistance.Witness

noncomputable section

def pairMassNestedPolynomialQ : Polynomial (Polynomial ℚ) :=
  ∑ i : Fin 4, Polynomial.C
    (∑ j : Fin 4, Polynomial.C (pairPowerCoefficients i j) *
      Polynomial.X ^ (j : ℕ)) * Polynomial.X ^ (i : ℕ)

def pairMassNestedCoeffQ (P : Polynomial (Polynomial ℚ)) (i j : ℕ) : ℚ :=
  (P.coeff i).coeff j

def PairMassDenseRep (A : PairMassDense3) (P : Polynomial (Polynomial ℚ)) : Prop :=
  ∀ a b, a < 10 → b < 10 →
    pairMassDenseGet A a b = pairMassNestedCoeffQ P a b

theorem pairMassNestedCoeffQ_mul (P Q : Polynomial (Polynomial ℚ)) (a b : ℕ) :
    pairMassNestedCoeffQ (P * Q) a b =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        pairMassNestedCoeffQ P i j * pairMassNestedCoeffQ Q (a - i) (b - j) := by
  unfold pairMassNestedCoeffQ
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem pairMassDenseGet_ofFn (f : Fin 10 → Fin 10 → ℚ)
    {a b : ℕ} (ha : a < 10) (hb : b < 10) :
    pairMassDenseGet (pairMassDenseOfFn f) a b = f ⟨a, ha⟩ ⟨b, hb⟩ := by
  unfold pairMassDenseGet
  rw [dif_pos ha, dif_pos hb]
  change (pairMassDenseOfFn f)[a][b] = _
  unfold pairMassDenseOfFn
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]

theorem PairMassDenseRep.add {A B : PairMassDense3}
    {P Q : Polynomial (Polynomial ℚ)}
    (hA : PairMassDenseRep A P) (hB : PairMassDenseRep B Q) :
    PairMassDenseRep (pairMassDenseAdd A B) (P + Q) := by
  intro a b ha hb
  unfold pairMassDenseAdd
  rw [pairMassDenseGet_ofFn _ ha hb, hA a b ha hb, hB a b ha hb]
  simp [pairMassNestedCoeffQ]

theorem PairMassDenseRep.scale {A : PairMassDense3}
    {P : Polynomial (Polynomial ℚ)} (hA : PairMassDenseRep A P) (c : ℚ) :
    PairMassDenseRep (pairMassDenseScale c A)
      (Polynomial.C (Polynomial.C c) * P) := by
  intro a b ha hb
  unfold pairMassDenseScale
  rw [pairMassDenseGet_ofFn _ ha hb, hA a b ha hb]
  simp [pairMassNestedCoeffQ, Polynomial.coeff_C_mul]

theorem PairMassDenseRep.mul {A B : PairMassDense3}
    {P Q : Polynomial (Polynomial ℚ)}
    (hA : PairMassDenseRep A P) (hB : PairMassDenseRep B Q) :
    PairMassDenseRep (pairMassDenseMul A B) (P * Q) := by
  intro a b ha hb
  unfold pairMassDenseMul
  rw [pairMassDenseGet_ofFn _ ha hb, pairMassNestedCoeffQ_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA i j (by simp only [Finset.mem_range] at hi; omega)
      (by simp only [Finset.mem_range] at hj; omega),
    hB (a - i) (b - j) (by omega) (by omega)]

theorem pairMass_convolution_reflect (f g : ℕ → ℕ → ℚ) (a b : ℕ) :
    (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        f i j * g (a - i) (b - j)) =
      ∑ di ∈ Finset.range (a + 1), ∑ dj ∈ Finset.range (b + 1),
        f (a - di) (b - dj) * g di dj := by
  rw [← Finset.sum_range_reflect (fun i => ∑ j ∈ Finset.range (b + 1),
    f i j * g (a - i) (b - j)) (a + 1)]
  apply Finset.sum_congr rfl
  intro di hdi
  simp only [Finset.mem_range] at hdi
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self (Nat.le_of_lt_succ hdi)]
  rw [← Finset.sum_range_reflect (fun j => f (a - di) j * g di (b - j)) (b + 1)]
  apply Finset.sum_congr rfl
  intro dj hdj
  simp only [Finset.mem_range] at hdj
  congr 3 <;> omega

def PairMassDenseCubicSupport (A : PairMassDense3) : Prop :=
  ∀ a b, a < 10 → b < 10 → (4 ≤ a ∨ 4 ≤ b) → pairMassDenseGet A a b = 0

theorem PairMassDenseCubicSupport.add {A B : PairMassDense3}
    (hA : PairMassDenseCubicSupport A) (hB : PairMassDenseCubicSupport B) :
    PairMassDenseCubicSupport (pairMassDenseAdd A B) := by
  intro a b ha hb hout
  unfold pairMassDenseAdd
  rw [pairMassDenseGet_ofFn _ ha hb, hA a b ha hb hout, hB a b ha hb hout]
  norm_num

theorem PairMassDenseCubicSupport.scale {A : PairMassDense3}
    (hA : PairMassDenseCubicSupport A) (c : ℚ) :
    PairMassDenseCubicSupport (pairMassDenseScale c A) := by
  intro a b ha hb hout
  unfold pairMassDenseScale
  rw [pairMassDenseGet_ofFn _ ha hb, hA a b ha hb hout]
  norm_num

theorem pairMassDenseBase_cubicSupport :
    PairMassDenseCubicSupport pairMassDenseBase := by
  intro a b ha hb hout
  unfold pairMassDenseBase
  rw [pairMassDenseGet_ofFn _ ha hb]
  rcases hout with ha4 | hb4
  · simp [show ¬a < 4 by omega]
  · by_cases ha' : a < 4
    · simp [ha', show ¬b < 4 by omega]
    · simp [ha']

theorem pairMassDenseOne_cubicSupport :
    PairMassDenseCubicSupport pairMassDenseOne := by
  intro a b ha hb hout
  unfold pairMassDenseOne
  rw [pairMassDenseGet_ofFn _ ha hb]
  simp only [ite_eq_right_iff]
  intro hab
  omega

theorem pairMassDenseCentered_cubicSupport (i j : Fin 8) :
    PairMassDenseCubicSupport (pairMassDenseCentered i j) := by
  unfold pairMassDenseCentered
  exact (pairMassDenseBase_cubicSupport.scale _).add
    (pairMassDenseOne_cubicSupport.scale _)

theorem PairMassDenseRep.mulCubic {A B : PairMassDense3}
    {P Q : Polynomial (Polynomial ℚ)}
    (hA : PairMassDenseRep A P) (hB : PairMassDenseRep B Q)
    (hsupp : PairMassDenseCubicSupport B) :
    PairMassDenseRep (pairMassDenseMulCubic A B) (P * Q) := by
  intro a b ha hb
  unfold pairMassDenseMulCubic
  rw [pairMassDenseGet_ofFn _ ha hb, pairMassNestedCoeffQ_mul,
    pairMass_convolution_reflect]
  apply Finset.sum_congr rfl
  intro di hdi
  apply Finset.sum_congr rfl
  intro dj hdj
  simp only [Finset.mem_range] at hdi hdj
  rw [← hA (a - di) (b - dj) (by omega) (by omega),
    ← hB di dj (by omega) (by omega)]
  by_cases hdi4 : di < 4 <;> by_cases hdj4 : dj < 4
  · simp [hdi4, hdj4]
  · simp [hdi4, hdj4, hsupp di dj (by omega) (by omega) (by omega)]
  · simp [hdi4, hdj4, hsupp di dj (by omega) (by omega) (by omega)]
  · simp [hdi4, hdj4, hsupp di dj (by omega) (by omega) (by omega)]

theorem pairMassDenseOne_rep :
    PairMassDenseRep pairMassDenseOne (1 : Polynomial (Polynomial ℚ)) := by
  intro a b ha hb
  unfold pairMassDenseOne
  rw [pairMassDenseGet_ofFn _ ha hb]
  simp [pairMassDenseOne, pairMassNestedCoeffQ]
  aesop

theorem PairMassDenseRep.pow {A : PairMassDense3}
    {P : Polynomial (Polynomial ℚ)} (hA : PairMassDenseRep A P) (k : ℕ) :
    PairMassDenseRep (pairMassDensePow A k) (P ^ k) := by
  induction k with
  | zero => simpa [pairMassDensePow] using pairMassDenseOne_rep
  | succ k ih => simpa [pairMassDensePow, pow_succ] using ih.mul hA

theorem pairMassNestedRowCoeffQ (i : Fin 4) (b : ℕ) :
    (∑ j : Fin 4, Polynomial.C (pairPowerCoefficients i j) *
      Polynomial.X ^ (j : ℕ)).coeff b =
      if hb : b < 4 then pairPowerCoefficients i ⟨b, hb⟩ else 0 := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hb : b < 4
  · rw [dif_pos hb]
    let bj : Fin 4 := ⟨b, hb⟩
    rw [Finset.sum_eq_single bj]
    · simp [bj]
    · intro j _ hj
      have hne : b ≠ (j : ℕ) := by
        intro h
        apply hj
        apply Fin.ext
        exact h.symm
      simp [hne]
    · simp
  · rw [dif_neg hb]
    apply Finset.sum_eq_zero
    intro j _
    have hne : b ≠ (j : ℕ) := by omega
    simp [hne]

theorem pairMassNestedPolynomialQ_coeff (a : ℕ) :
    pairMassNestedPolynomialQ.coeff a =
      if ha : a < 4 then
        ∑ j : Fin 4, Polynomial.C (pairPowerCoefficients ⟨a, ha⟩ j) *
          Polynomial.X ^ (j : ℕ)
      else 0 := by
  unfold pairMassNestedPolynomialQ
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases ha : a < 4
  · rw [dif_pos ha]
    let ai : Fin 4 := ⟨a, ha⟩
    rw [Finset.sum_eq_single ai]
    · simp [ai]
    · intro i _ hi
      have hne : a ≠ (i : ℕ) := by
        intro h
        apply hi
        apply Fin.ext
        exact h.symm
      simp [hne]
    · simp
  · rw [dif_neg ha]
    apply Finset.sum_eq_zero
    intro i _
    have hne : a ≠ (i : ℕ) := by omega
    simp [hne]

theorem pairMassNestedCoeffQ_base (a b : ℕ) :
    pairMassNestedCoeffQ pairMassNestedPolynomialQ a b =
      if ha : a < 4 then
        if hb : b < 4 then pairPowerCoefficients ⟨a, ha⟩ ⟨b, hb⟩ else 0
      else 0 := by
  unfold pairMassNestedCoeffQ
  rw [pairMassNestedPolynomialQ_coeff]
  split <;> rename_i ha
  · exact pairMassNestedRowCoeffQ ⟨a, ha⟩ b
  · simp

theorem pairMassDenseBase_rep :
    PairMassDenseRep pairMassDenseBase pairMassNestedPolynomialQ := by
  intro a b ha hb
  unfold pairMassDenseBase
  rw [pairMassDenseGet_ofFn _ ha hb, pairMassNestedCoeffQ_base]

def pairMassCenteredPolynomialQ (i j : Fin 8) : Polynomial (Polynomial ℚ) :=
  Polynomial.C (Polynomial.C (pairMassCellCenterQ i j)⁻¹) *
      pairMassNestedPolynomialQ +
    Polynomial.C (Polynomial.C (-1)) * 1

def pairMassBracketPolynomialQ (i j : Fin 8) : Polynomial (Polynomial ℚ) :=
  Polynomial.C (Polynomial.C (pairMassChooseQ 0)) *
      pairMassCenteredPolynomialQ i j ^ 0 +
    Polynomial.C (Polynomial.C (pairMassChooseQ 1)) *
      pairMassCenteredPolynomialQ i j ^ 1 +
    (Polynomial.C (Polynomial.C (pairMassChooseQ 2)) *
        pairMassCenteredPolynomialQ i j ^ 2 +
      Polynomial.C (Polynomial.C (pairMassChooseQ 3)) *
        pairMassCenteredPolynomialQ i j ^ 3 +
      Polynomial.C (Polynomial.C (pairMassTailQ i j)) * 1)

def pairMassExpandedBracketPolynomialQ (i j : Fin 8) :
    Polynomial (Polynomial ℚ) :=
  Polynomial.C (Polynomial.C (pairMassBracketConstantQ i j)) * 1 +
    Polynomial.C (Polynomial.C (pairMassBracketLinearQ i j)) *
      pairMassNestedPolynomialQ +
    (Polynomial.C (Polynomial.C (pairMassBracketQuadraticQ i j)) *
        pairMassNestedPolynomialQ ^ 2 +
      Polynomial.C (Polynomial.C (pairMassBracketCubicQ i j)) *
        pairMassNestedPolynomialQ ^ 3)

theorem pairMassDenseCentered_rep (i j : Fin 8) :
    PairMassDenseRep (pairMassDenseCentered i j)
      (pairMassCenteredPolynomialQ i j) := by
  unfold pairMassDenseCentered pairMassCenteredPolynomialQ
  exact (pairMassDenseBase_rep.scale _).add (pairMassDenseOne_rep.scale _)

theorem pairMassDenseSquare_rep (i j : Fin 8) :
    PairMassDenseRep (pairMassDenseSquare i j)
      (pairMassCenteredPolynomialQ i j ^ 2) := by
  unfold pairMassDenseSquare
  simpa [pow_two] using (pairMassDenseCentered_rep i j).mulCubic
    (pairMassDenseCentered_rep i j) (pairMassDenseCentered_cubicSupport i j)

theorem pairMassDenseCube_rep (i j : Fin 8) :
    PairMassDenseRep (pairMassDenseCube i j)
      (pairMassCenteredPolynomialQ i j ^ 3) := by
  unfold pairMassDenseCube
  simpa [pow_succ, pow_two] using (pairMassDenseSquare_rep i j).mulCubic
    (pairMassDenseCentered_rep i j) (pairMassDenseCentered_cubicSupport i j)

theorem pairMassDenseBaseSquare_rep :
    PairMassDenseRep pairMassDenseBaseSquare (pairMassNestedPolynomialQ ^ 2) := by
  unfold pairMassDenseBaseSquare
  simpa [pow_two] using pairMassDenseBase_rep.mulCubic pairMassDenseBase_rep
    pairMassDenseBase_cubicSupport

theorem pairMassDenseBaseCube_rep :
    PairMassDenseRep pairMassDenseBaseCube (pairMassNestedPolynomialQ ^ 3) := by
  unfold pairMassDenseBaseCube
  simpa [pow_succ, pow_two] using pairMassDenseBaseSquare_rep.mulCubic
    pairMassDenseBase_rep pairMassDenseBase_cubicSupport

theorem pairMassDenseBaseSquareData_rep :
    PairMassDenseRep pairMassDenseBaseSquareData
      (pairMassNestedPolynomialQ ^ 2) := by
  rw [← pairMassDenseBaseSquare_eq_data]
  exact pairMassDenseBaseSquare_rep

theorem pairMassDenseBaseCubeData_rep :
    PairMassDenseRep pairMassDenseBaseCubeData
      (pairMassNestedPolynomialQ ^ 3) := by
  rw [← pairMassDenseBaseCube_eq_data]
  exact pairMassDenseBaseCube_rep

theorem pairMassDenseBracket3_rep (i j : Fin 8) :
    PairMassDenseRep (pairMassDenseBracket3 i j)
      (pairMassBracketPolynomialQ i j) := by
  have hexp : PairMassDenseRep (pairMassDenseBracket3 i j)
      (pairMassExpandedBracketPolynomialQ i j) := by
    unfold pairMassDenseBracket3 pairMassExpandedBracketPolynomialQ
    exact (pairMassDenseOne_rep.scale _).add
      (pairMassDenseBase_rep.scale _) |>.add
        ((pairMassDenseBaseSquare_rep.scale _).add
          (pairMassDenseBaseCube_rep.scale _))
  have heq : pairMassExpandedBracketPolynomialQ i j =
      pairMassBracketPolynomialQ i j := by
    have hCinvPow (q : ℚ) (n : ℕ) :
        Polynomial.C (Polynomial.C ((q ^ n)⁻¹)) =
          (Polynomial.C (Polynomial.C q⁻¹) :
            Polynomial (Polynomial ℚ)) ^ n := by
      rw [← inv_pow]
      rw [Polynomial.C_pow, Polynomial.C_pow]
    unfold pairMassExpandedBracketPolynomialQ pairMassBracketPolynomialQ
      pairMassCenteredPolynomialQ pairMassBracketConstantQ
      pairMassBracketLinearQ pairMassBracketQuadraticQ pairMassBracketCubicQ
    norm_num
    rw [hCinvPow (pairMassCellCenterQ i j) 2,
      hCinvPow (pairMassCellCenterQ i j) 3]
    simp only [Polynomial.C_ofNat]
    ring
  rwa [heq] at hexp

theorem pairMassPowerInnerQ3_eq_data_apply
    (r : Fin 4) (j : Fin 8) (t : Fin 2) (a : Fin 10) :
    pairMassPowerInnerQ3 r j t a = pairMassPowerInnerData3 r j t a := by
  have h := congrArg (fun v : Vector ℚ 10 => v[a.val])
    (pairMassPowerInnerQ3_eq_data r j t)
  simpa only [Vector.getElem_ofFn] using h

theorem pairMassStagedPowerContractionQ3_eq_data_apply
    (r : Fin 4) (i j : Fin 8) (s t : Fin 2) :
    pairMassStagedPowerContractionQ3 r i j s t =
      pairMassPowerContractionData3 r i j s t := by
  have h := congrArg (fun v : Vector ℚ 2 => v[t.val])
    (pairMassStagedPowerContractionQ3_eq_data r i j s)
  simpa only [Vector.getElem_ofFn] using h

theorem pairMassDensePowerContraction3_matrixData_eq
    (r : Fin 4) (i j : Fin 8) (s t : Fin 2) :
    pairMassDensePowerContraction3 (pairMassPowerMatrixData3 r) i j s t =
      pairMassPowerContractionData3 r i j s t := by
  rw [← pairMassStagedPowerContractionQ3_eq_data_apply]
  unfold pairMassDensePowerContraction3 pairMassStagedPowerContractionQ3
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.mem_range] at ha
  rw [dif_pos ha, ← pairMassPowerInnerQ3_eq_data_apply]
  unfold pairMassPowerInnerQ3
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem pairMassDenseGet_add (A B : PairMassDense3) {a b : ℕ}
    (ha : a < 10) (hb : b < 10) :
    pairMassDenseGet (pairMassDenseAdd A B) a b =
      pairMassDenseGet A a b + pairMassDenseGet B a b := by
  unfold pairMassDenseAdd
  rw [pairMassDenseGet_ofFn _ ha hb]

theorem pairMassDenseGet_scale (c : ℚ) (A : PairMassDense3) {a b : ℕ}
    (ha : a < 10) (hb : b < 10) :
    pairMassDenseGet (pairMassDenseScale c A) a b =
      c * pairMassDenseGet A a b := by
  unfold pairMassDenseScale
  rw [pairMassDenseGet_ofFn _ ha hb]

theorem pairMassDensePowerContraction3_add (A B : PairMassDense3)
    (i j : Fin 8) (s t : Fin 2) :
    pairMassDensePowerContraction3 (pairMassDenseAdd A B) i j s t =
      pairMassDensePowerContraction3 A i j s t +
        pairMassDensePowerContraction3 B i j s t := by
  unfold pairMassDensePowerContraction3
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [pairMassDenseGet_add A B (by simp only [Finset.mem_range] at ha; omega)
    (by simp only [Finset.mem_range] at hb; omega)]
  ring

theorem pairMassDensePowerContraction3_scale (c : ℚ) (A : PairMassDense3)
    (i j : Fin 8) (s t : Fin 2) :
    pairMassDensePowerContraction3 (pairMassDenseScale c A) i j s t =
      c * pairMassDensePowerContraction3 A i j s t := by
  unfold pairMassDensePowerContraction3
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [pairMassDenseGet_scale c A (by simp only [Finset.mem_range] at ha; omega)
    (by simp only [Finset.mem_range] at hb; omega)]
  ring

theorem pairMassDensePowerMatrixData3_zero :
    pairMassPowerMatrixData3 ⟨0, by decide⟩ = pairMassDenseOne := rfl

theorem pairMassDensePowerMatrixData3_one :
    pairMassPowerMatrixData3 ⟨1, by decide⟩ = pairMassDenseBase := rfl

theorem pairMassDensePowerMatrixData3_two :
    pairMassPowerMatrixData3 ⟨2, by decide⟩ = pairMassDenseBaseSquareData := rfl

theorem pairMassDensePowerMatrixData3_three :
    pairMassPowerMatrixData3 ⟨3, by decide⟩ = pairMassDenseBaseCubeData := rfl

theorem pairMassBracketScalarsQ_eq_data_apply
    (i j : Fin 8) (r : Fin 4) :
    (#v[pairMassBracketConstantQ i j, pairMassBracketLinearQ i j,
      pairMassBracketQuadraticQ i j, pairMassBracketCubicQ i j] : Vector ℚ 4).get r =
      pairMassBracketScalarDataQ3 r i j := by
  have h := congrArg (fun v : Vector ℚ 4 => v[r.val])
    (pairMassBracketScalarsQ_eq_data i j)
  have hget :
      (#v[pairMassBracketConstantQ i j, pairMassBracketLinearQ i j,
        pairMassBracketQuadraticQ i j, pairMassBracketCubicQ i j] :
          Vector ℚ 4).get r =
        (#v[pairMassBracketConstantQ i j, pairMassBracketLinearQ i j,
          pairMassBracketQuadraticQ i j, pairMassBracketCubicQ i j] :
            Vector ℚ 4)[r.val] := rfl
  rw [hget]
  simpa only [Vector.getElem_ofFn] using h

theorem pairMassDenseBracket3_contraction_eq_declared
    (i j : Fin 8) (s t : Fin 2) :
    pairMassDensePowerContraction3 (pairMassDenseBracket3 i j) i j s t =
      pairMassContractionCoefficient3 i j s t := by
  have hcell := congrArg (fun v : Vector (Vector ℚ 2) 2 => v[s.val][t.val])
    (pairMassDenseCellCoefficients3_eq_declared i j)
  simp only [pairMassDenseCellCoefficients3, Vector.getElem_ofFn] at hcell
  unfold pairMassDenseBracket3
  rw [pairMassDensePowerContraction3_add,
    pairMassDensePowerContraction3_add,
    pairMassDensePowerContraction3_scale,
    pairMassDensePowerContraction3_scale,
    pairMassDensePowerContraction3_add,
    pairMassDensePowerContraction3_scale,
    pairMassDensePowerContraction3_scale]
  have h0 : pairMassBracketConstantQ i j =
      pairMassBracketScalarDataQ3 ⟨0, by decide⟩ i j := by
    have h := congrArg (fun v : Vector ℚ 4 => v.toArray[0])
      (pairMassBracketScalarsQ_eq_data i j)
    simpa using h
  have h1 : pairMassBracketLinearQ i j =
      pairMassBracketScalarDataQ3 ⟨1, by decide⟩ i j := by
    have h := congrArg (fun v : Vector ℚ 4 => v.toArray[1])
      (pairMassBracketScalarsQ_eq_data i j)
    simpa using h
  have h2 : pairMassBracketQuadraticQ i j =
      pairMassBracketScalarDataQ3 ⟨2, by decide⟩ i j := by
    have h := congrArg (fun v : Vector ℚ 4 => v.toArray[2])
      (pairMassBracketScalarsQ_eq_data i j)
    simpa using h
  have h3 : pairMassBracketCubicQ i j =
      pairMassBracketScalarDataQ3 ⟨3, by decide⟩ i j := by
    have h := congrArg (fun v : Vector ℚ 4 => v.toArray[3])
      (pairMassBracketScalarsQ_eq_data i j)
    simpa using h
  rw [h0, h1, h2, h3]
  rw [← pairMassDensePowerMatrixData3_zero,
    pairMassDensePowerContraction3_matrixData_eq,
    ← pairMassDensePowerMatrixData3_one,
    pairMassDensePowerContraction3_matrixData_eq]
  rw [pairMassDenseBaseSquare_eq_data]
  rw [← pairMassDensePowerMatrixData3_two,
    pairMassDensePowerContraction3_matrixData_eq]
  rw [pairMassDenseBaseCube_eq_data]
  rw [← pairMassDensePowerMatrixData3_three,
    pairMassDensePowerContraction3_matrixData_eq]
  simpa only [Fin.eta, add_assoc] using hcell


end

end UnitDistance.Witness
