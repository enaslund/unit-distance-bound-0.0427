module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import UnitDistance.RelativeDiscriminant

@[expose] public section
set_option backward.privateInPublic true


/-! Numerical invariants of isomorphic number fields. The ideal correspondence
preserves every norm, so it identifies the full defining Dirichlet series,
including the total-function convention outside its convergence region. -/

noncomputable section
open NumberField

namespace UnitDistance.NumberFieldAnalysis

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- The actual ideal correspondence induced by a field isomorphism. -/
def idealsEquiv (e : K ≃ₐ[ℚ] L) : Ideal (𝓞 K) ≃ Ideal (𝓞 L) :=
  (RingOfIntegers.mapRingEquiv e.toRingEquiv).idealComapOrderIso.symm.toEquiv

theorem idealsEquiv_absNorm (e : K ≃ₐ[ℚ] L) (I : Ideal (𝓞 K)) :
    Ideal.absNorm (idealsEquiv e I) = Ideal.absNorm I := by
  let f := RingOfIntegers.mapRingEquiv e.toRingEquiv
  change Ideal.absNorm (I.map f) = Ideal.absNorm I
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).symm.toEquiv

theorem norm_ideal_card_eq (e : K ≃ₐ[ℚ] L) (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} := by
  apply Nat.card_congr
  exact (idealsEquiv e).subtypeEquiv (fun I => by rw [idealsEquiv_absNorm])

/-- Equality of the independently defined Dedekind zeta functions as functions. -/
theorem dedekindZeta_eq_of_algEquiv (e : K ≃ₐ[ℚ] L) :
    dedekindZeta K = dedekindZeta L := by
  funext s
  unfold dedekindZeta
  congr 1
  funext n
  rw [norm_ideal_card_eq e]

theorem logDeriv_dedekindZeta_eq_of_algEquiv (e : K ≃ₐ[ℚ] L) (s : ℂ) :
    logDeriv (dedekindZeta K) s = logDeriv (dedekindZeta L) s := by
  rw [dedekindZeta_eq_of_algEquiv e]

theorem absoluteDiscriminant_eq_of_algEquiv (e : K ≃ₐ[ℚ] L) :
    absoluteDiscriminant K = absoluteDiscriminant L := by
  unfold absoluteDiscriminant
  rw [NumberField.discr_eq_discr_of_algEquiv K e]

theorem rootDiscriminant_eq_of_algEquiv (e : K ≃ₐ[ℚ] L) :
    rootDiscriminant K = rootDiscriminant L := by
  unfold rootDiscriminant
  rw [absoluteDiscriminant_eq_of_algEquiv e, e.toLinearEquiv.finrank_eq]

end UnitDistance.NumberFieldAnalysis
