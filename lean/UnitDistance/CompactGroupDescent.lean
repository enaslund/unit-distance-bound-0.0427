module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Continuous descent through a surjection from a compact group. -/
noncomputable section
namespace UnitDistance.CompactGroup
variable {G Q P : Type*} [Group G] [Group Q] [Group P]
  [TopologicalSpace G] [TopologicalSpace Q] [TopologicalSpace P]
  [CompactSpace G] [T2Space Q]
variable (q : G →ₜ* Q) (hq : Function.Surjective q)
  (f : G →ₜ* P) (hf : q.toMonoidHom.ker≤f.toMonoidHom.ker)

/-- Algebraic descent is continuous because a compact Hausdorff surjection
is a quotient map. -/
def descent : Q →ₜ* P := by
  let m : Q →* P := q.toMonoidHom.liftOfSurjective hq ⟨f.toMonoidHom,hf⟩
  refine {toMonoidHom := m, continuous_toFun := ?_}
  apply (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous_toFun).continuous_iff.mpr
  have he : (fun x=>m (q x))=f := by
    funext x
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  change Continuous (fun x=>m (q x))
  rw [he]
  exact f.continuous_toFun

@[simp] theorem descent_apply (g : G) : descent q hq f hf (q g)=f g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem descent_comp : (descent q hq f hf).comp q=f := by
  ext g
  exact descent_apply q hq f hf g

theorem descent_surjective (hs : Function.Surjective f) :
    Function.Surjective (descent q hq f hf) := by
  intro p
  obtain ⟨g,rfl⟩ := hs p
  exact ⟨q g,descent_apply q hq f hf g⟩

end UnitDistance.CompactGroup
