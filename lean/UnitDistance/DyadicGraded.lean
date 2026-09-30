module

public import UnitDistance.DyadicGradedCertificates

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual dyadic associated graded Fox-row kernel

Both multiplication orientations on the true augmentation quotients are
injective below degree seven. The right-multiplication convention is the one
used for multiplication of a variable coefficient into the manuscript's left
Fox row. No Galois realization or ambient filtration compatibility is assumed
or inferred here.
-/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Dyadic.AlgebraD
open Graded

theorem sided_graded_kernel (n : ℕ) (hn : n < 7) (left : Bool)
    (v : AlgebraD) (hv : v ∈ augmentationPower n) :
    (∀ k, sidedProduct left k v ∈ augmentationPower (n + 2)) ↔
      v ∈ augmentationPower (n + 1) := by
  have h := Graded.gradedKernel_below_seven n hn left (Filtration.coefficients v)
    ((coefficients_mem_stage n v).mpr hv)
  simpa only [sidedStep_coefficients, coefficients_mem_stage] using h

def multiplicationOnPower (left : Bool) (n : ℕ) (k : Fin 3) :
    augmentationPower n →ₗ[F] augmentationPower (n + 1) where
  toFun v := ⟨sidedProduct left k v.val, sidedProduct_mem_power left k n v.val v.property⟩
  map_add' u v := by
    apply Subtype.ext
    cases left <;> simp [sidedProduct, mul_add, add_mul]
  map_smul' c v := by
    apply Subtype.ext
    cases left <;> simp [sidedProduct]

/-- The ordinary induced map `Jⁿ/Jⁿ⁺¹ → (Jⁿ⁺¹/Jⁿ⁺²)³`, with multiplication
by the three actual generator differences. -/
def gradedMultiplication (left : Bool) (n : ℕ) :
    augmentationLayer n →ₗ[F] (Fin 3 → augmentationLayer (n + 1)) :=
  LinearMap.pi fun k =>
    ((augmentationPower (n + 1)).comap (augmentationPower n).subtype).mapQ
      ((augmentationPower (n + 1 + 1)).comap (augmentationPower (n + 1)).subtype)
      (multiplicationOnPower left n k) (by
        intro v hv
        exact sidedProduct_mem_power left k (n + 1) v.val hv)

theorem gradedMultiplication_mk (left : Bool) (n : ℕ) (v : augmentationPower n)
    (k : Fin 3) :
    gradedMultiplication left n (Submodule.Quotient.mk v) k =
      Submodule.Quotient.mk (multiplicationOnPower left n k v) := rfl

/-- Exact injectivity on the actual associated graded spaces, below the socle. -/
theorem gradedMultiplication_injective (left : Bool) (n : ℕ) (hn : n < 7) :
    Function.Injective (gradedMultiplication left n) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_bot_iff.mp
  intro v hv
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (sided_graded_kernel n hn left v.val v.property).mp
    intro k
    have hk := congrFun hv k
    rw [gradedMultiplication_mk] at hk
    exact (Submodule.Quotient.mk_eq_zero
      ((augmentationPower (n + 2)).comap (augmentationPower (n + 1)).subtype)).mp hk

/-- At degree seven the entire one-dimensional source is the kernel. -/
theorem gradedMultiplication_seven_eq_zero (left : Bool) :
    gradedMultiplication left 7 = 0 := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    ext k
    rw [gradedMultiplication_mk]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have h := sidedProduct_mem_power left k 7 v.val v.property
    rw [augmentation_eighth_eq_bot] at h
    change sidedProduct left k v.val ∈ augmentationPower 9
    rw [show sidedProduct left k v.val = 0 from h]
    exact Submodule.zero_mem _

theorem finrank_gradedMultiplication_seven_kernel (left : Bool) :
    Module.finrank F (gradedMultiplication left 7).ker = 1 := by
  rw [gradedMultiplication_seven_eq_zero, LinearMap.ker_zero, finrank_top,
    finrank_augmentationLayer]
  have h7 : Module.finrank F (augmentationPower 7) = 1 := augmentation_dimensions 7
  have h8 : Module.finrank F (augmentationPower 8) = 0 := augmentation_dimensions 8
  rw [h7, h8]

/-- The three degree-one Fox coefficients of the displayed quadratic initial
`y² + [x,y] + [x,z]`, where each letter is a generator difference. -/
def linearFoxCoefficients : Fin 3 → AlgebraD :=
  ![(delta D.y - 1) + (delta D.z - 1),
    (delta D.y - 1) + (delta D.x - 1), delta D.x - 1]

theorem linearFox_mem_iff (S : Submodule F AlgebraD) (v : AlgebraD) :
    (∀ k, v * linearFoxCoefficients k ∈ S) ↔
      ∀ k, v * (delta (Filtration.gen k) - 1) ∈ S := by
  constructor
  · intro h
    have hx : v * (delta D.x - 1) ∈ S := h 2
    have hy : v * (delta D.y - 1) ∈ S := by
      have hm := S.sub_mem (h 1) hx
      simpa [linearFoxCoefficients, mul_add] using hm
    have hz : v * (delta D.z - 1) ∈ S := by
      have hm := S.sub_mem (h 0) hy
      simpa [linearFoxCoefficients, mul_add] using hm
    intro k
    fin_cases k
    · exact hx
    · exact hy
    · exact hz
  · intro h k
    fin_cases k
    · simpa [linearFoxCoefficients, Filtration.gen, mul_add] using S.add_mem (h 1) (h 2)
    · simpa [linearFoxCoefficients, Filtration.gen, mul_add] using S.add_mem (h 1) (h 0)
    · exact h 0

/-- Right multiplication by an element of `J²` raises augmentation degree by
at least two. This connects the initial Fox coefficients to arbitrary actual
coefficients with the same first-order terms. -/
theorem power_mul_square (n : ℕ) (v a : AlgebraD)
    (hv : v ∈ augmentationPower n) (ha : a ∈ augmentationPower 2) :
    v * a ∈ augmentationPower (n + 2) := by
  change a ∈ Submodule.span F {a | ∃ u ∈ augmentationPower 1,
    ∃ b, augmentation b = 0 ∧ a = u * b} at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨u, hu, b, hb, rfl⟩
    rw [augmentationPower_one] at hu
    rw [← mul_assoc]
    exact power_mul_augmentation (n + 1) _ b (power_mul_augmentation n v u hv hu) hb
  | zero => simp
  | add a b ha hb iha ihb =>
    simpa only [mul_add] using (augmentationPower (n + 2)).add_mem iha ihb
  | smul c a ha iha =>
    simpa only [mul_smul_comm] using (augmentationPower (n + 2)).smul_mem c iha

/-- The exact finite algebra conclusion needed for any actual defining Fox
row whose first-order terms are the displayed coefficients. The congruence
hypothesis is an ordinary, independently meaningful statement modulo `J²`;
identifying a local Galois relation with such a row remains separate. -/
theorem fox_row_graded_kernel (c : Fin 3 → AlgebraD)
    (hc : ∀ k, c k - linearFoxCoefficients k ∈ augmentationPower 2)
    (n : ℕ) (hn : n < 7) (v : AlgebraD) (hv : v ∈ augmentationPower n) :
    (∀ k, v * c k ∈ augmentationPower (n + 2)) ↔ v ∈ augmentationPower (n + 1) := by
  have hlin : (∀ k, v * c k ∈ augmentationPower (n + 2)) ↔
      ∀ k, v * linearFoxCoefficients k ∈ augmentationPower (n + 2) := by
    constructor
    · intro h k
      have hd := power_mul_square n v (c k - linearFoxCoefficients k) hv (hc k)
      have hm := (augmentationPower (n + 2)).sub_mem (h k) hd
      simpa only [mul_sub, sub_sub_cancel] using hm
    · intro h k
      have hd := power_mul_square n v (c k - linearFoxCoefficients k) hv (hc k)
      have hm := (augmentationPower (n + 2)).add_mem hd (h k)
      simpa only [mul_sub, sub_add_cancel] using hm
  rw [hlin, linearFox_mem_iff]
  exact sided_graded_kernel n hn false v hv

end UnitDistance.Dyadic.AlgebraD
