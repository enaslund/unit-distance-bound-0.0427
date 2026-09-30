module

public import UnitDistance.GeneratedQuadraticTower

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual automorphisms of generated quadratic towers

Automorphisms are determined by their restriction to the actual base field
and their action on its selected square roots. The actual relative kernel
has exponent two; invariant base squareclasses make that kernel central.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.Multiquadratic
universe u
variable {ι : Type*} [DecidableEq ι] {E : Type u} [Field E] [CharZero E]
  {k : Type*} [Field k] [Algebra k E]
  {a : ι → E} {s : Finset ι} (T : GeneratedGaloisTower k a s)

/-- Agreement on the base field and all actual selected radicals determines
the actual field automorphism. -/
theorem GeneratedGaloisTower.aut_ext (σ τ : Gal(T.Carrier/k))
    (hbase : ∀ x : E, σ (algebraMap E T.Carrier x) = τ (algebraMap E T.Carrier x))
    (hroots : ∀ x ∈ radicalSet (L := T.Carrier) a s, σ x = τ x) : σ = τ := by
  let S : Subalgebra E T.Carrier := {
    carrier := {x | σ x = τ x}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := by
      intro x y hx hy
      change σ x = τ x at hx
      change σ y = τ y at hy
      change σ (x+y) = τ (x+y)
      simp only [map_add,hx,hy]
    mul_mem' := by
      intro x y hx hy
      change σ x = τ x at hx
      change σ y = τ y at hy
      change σ (x*y) = τ (x*y)
      simp only [map_mul,hx,hy]
    algebraMap_mem' := hbase }
  have hle : Algebra.adjoin E (radicalSet (L := T.Carrier) a s) ≤ S :=
    Algebra.adjoin_le_iff.mpr hroots
  rw [T.generated] at hle
  ext x
  exact hle (show x ∈ (⊤ : Subalgebra E T.Carrier) from trivial)

/-- Every actual automorphism fixing the base has exponent at most two. -/
theorem GeneratedGaloisTower.aut_sq_eq_one (σ : Gal(T.Carrier/k))
    (hbase : ∀ x : E, σ (algebraMap E T.Carrier x) = algebraMap E T.Carrier x) :
    σ^2 = 1 := by
  apply T.aut_ext
  · intro x
    simp [pow_two,AlgEquiv.mul_apply,hbase]
  · rintro x ⟨i,hi,hx⟩
    have hs : (σ x)^2 = x^2 := by rw [← map_pow,hx,hbase]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · simp [pow_two,AlgEquiv.mul_apply,h]
    · simp [pow_two,AlgEquiv.mul_apply,h,map_neg]

/-- Actual invariant squareclasses force the actual relative kernel to be
central in the entire ground-field Galois group. -/
theorem GeneratedGaloisTower.aut_commute [IsGalois k E]
    (hinvariant : ∀ i ∈ s, ∀ τ : Gal(E/k), ∃ u : E, a i*u^2 = τ (a i))
    (σ τ : Gal(T.Carrier/k))
    (hbase : ∀ x : E, σ (algebraMap E T.Carrier x) = algebraMap E T.Carrier x) :
    Commute σ τ := by
  change σ*τ = τ*σ
  apply T.aut_ext
  · intro x
    rw [AlgEquiv.mul_apply,AlgEquiv.mul_apply,hbase,
      ← AlgEquiv.restrictNormal_commutes τ E x,hbase]
  · rintro x ⟨i,hi,hx⟩
    have hs : (σ x)^2 = x^2 := by rw [← map_pow,hx,hbase]
    obtain ⟨u,hu⟩ := hinvariant i hi (τ.restrictNormal E)
    have ht : (τ x)^2 = (algebraMap E T.Carrier u*x)^2 := by
      rw [← map_pow,hx,← AlgEquiv.restrictNormal_commutes τ E (a i),← hu,
        map_mul,map_pow,mul_pow,hx]
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht with ht | ht <;>
      simp [AlgEquiv.mul_apply,hs,ht,map_mul,map_neg,hbase]

end UnitDistance.Multiquadratic
