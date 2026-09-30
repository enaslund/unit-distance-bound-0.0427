module

public import UnitDistance.CompactGroupDescent
public import UnitDistance.GaloisFiniteQuotientField

@[expose] public section
set_option backward.privateInPublic true


/-! The actual continuous finite Galois quotient of every intermediate field
whose fixing subgroup contains the kernel of a compact Galois quotient. -/
noncomputable section
namespace UnitDistance.GaloisQuotient
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [T2Space Q]
variable (q : Gal(Ω/k) →ₜ* Q) (hq : Function.Surjective q)
  (L : IntermediateField k Ω) [Module.Finite k L] [IsGalois k L]
  (hL : q.toMonoidHom.ker≤L.fixingSubgroup)

/-- Restriction to the actual field descends to a continuous quotient map. -/
def quotientToLayer : Q →ₜ* Gal(L/k) :=
  CompactGroup.descent q hq (GaloisEmbedding.restriction L.val)
    (by rw [restriction_kernel]; exact hL)

@[simp] theorem quotientToLayer_apply (g : Gal(Ω/k)) :
    quotientToLayer q hq L hL (q g)=GaloisEmbedding.restriction L.val g :=
  CompactGroup.descent_apply ..

theorem quotientToLayer_comp : (quotientToLayer q hq L hL).comp q=
    GaloisEmbedding.restriction L.val := CompactGroup.descent_comp ..

theorem quotientToLayer_surjective : Function.Surjective (quotientToLayer q hq L hL) :=
  CompactGroup.descent_surjective _ _ _ _ (GaloisEmbedding.restriction_surjective L.val)

end UnitDistance.GaloisQuotient
