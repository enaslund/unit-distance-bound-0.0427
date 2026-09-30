module

public import UnitDistance.GaloisEmbeddingRestriction
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section
set_option backward.privateInPublic true


/-! Realize a genuine finite continuous Galois quotient as an actual finite
intermediate field, and recover its map from every containing layer. -/
noncomputable section
namespace UnitDistance.GaloisQuotient
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {C : Type*} [Group C] [Fintype C] [TopologicalSpace C] [DiscreteTopology C]
variable (χ : Gal(Ω/k) →ₜ* C)

/-- The actual fixed field of the kernel of the finite quotient. -/
def finiteQuotientField : IntermediateField k Ω := IntermediateField.fixedField χ.toMonoidHom.ker

theorem finiteQuotientField_fixing :
    (finiteQuotientField χ).fixingSubgroup = χ.toMonoidHom.ker := by
  let H : ClosedSubgroup Gal(Ω/k) :=
    {toSubgroup := χ.toMonoidHom.ker
     isClosed' := isClosed_singleton.preimage χ.continuous_toFun}
  exact InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω) H

instance finiteQuotientField_finite : Module.Finite k (finiteQuotientField χ) := by
  apply ((InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
    (k := k) (K := Ω) (L := finiteQuotientField χ)).mp ?_).1
  rw [finiteQuotientField_fixing]
  exact ⟨(isOpen_discrete ({1} : Set C)).preimage χ.continuous_toFun, inferInstance⟩

instance finiteQuotientField_galois : IsGalois k (finiteQuotientField χ) := by
  apply ((InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
    (k := k) (K := Ω) (L := finiteQuotientField χ)).mp ?_).2
  rw [finiteQuotientField_fixing]
  exact ⟨(isOpen_discrete ({1} : Set C)).preimage χ.continuous_toFun, inferInstance⟩

variable (L : IntermediateField k Ω) [Module.Finite k L] [IsGalois k L]

/-- The kernel of actual restriction consists exactly of automorphisms fixing
the literal intermediate field. -/
theorem restriction_kernel :
    (GaloisEmbedding.restriction L.val).toMonoidHom.ker = L.fixingSubgroup := by
  ext g
  rw [MonoidHom.mem_ker,IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    change GaloisEmbedding.restriction L.val g = 1 at h
    have he := GaloisEmbedding.restriction_commutes L.val g (⟨x,hx⟩ : L)
    rw [h] at he
    exact he.symm
  · intro h
    apply AlgEquiv.ext
    intro x
    apply L.val.injective
    change L.val (GaloisEmbedding.restriction L.val g x) = L.val x
    rw [GaloisEmbedding.restriction_commutes]
    exact h x x.2

/-- Containment of the fixed field makes the finite quotient descend to the
actual finite Galois group of the layer. -/
def finiteQuotientOnLayer (hL : finiteQuotientField χ ≤ L) : Gal(L/k) →* C :=
  (GaloisEmbedding.restriction L.val).toMonoidHom.liftOfSurjective
    (GaloisEmbedding.restriction_surjective L.val)
    ⟨χ.toMonoidHom,by
      rw [restriction_kernel]
      intro g hg
      rw [← finiteQuotientField_fixing]
      exact IntermediateField.fixingSubgroup_le hL hg⟩

@[simp] theorem finiteQuotientOnLayer_restriction
    (hL : finiteQuotientField χ ≤ L) (g : Gal(Ω/k)) :
    finiteQuotientOnLayer χ L hL (GaloisEmbedding.restriction L.val g) = χ g := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem finiteQuotientOnLayer_surjective (hχ : Function.Surjective χ)
    (hL : finiteQuotientField χ ≤ L) : Function.Surjective (finiteQuotientOnLayer χ L hL) := by
  intro z
  obtain ⟨g,rfl⟩ := hχ z
  exact ⟨GaloisEmbedding.restriction L.val g,finiteQuotientOnLayer_restriction χ L hL g⟩

end UnitDistance.GaloisQuotient
