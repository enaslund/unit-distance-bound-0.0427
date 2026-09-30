module

public import UnitDistance.ProfiniteGeneratedTameCompactness
public import UnitDistance.HomKernelTransfer

@[expose] public section
set_option backward.privateInPublic true


/-! Actual generation in every open normal quotient implies generation in
every continuous discrete image. The target need not be declared finite. -/
noncomputable section
namespace UnitDistance.ProfiniteTame

variable {G I D P : Type*} [Group G] [TopologicalSpace G]
  [Group I] [TopologicalSpace I] [Group D] [TopologicalSpace D]
  [Group P] [TopologicalSpace P] [DiscreteTopology P]

theorem discrete_image_generates (i : I →ₜ* G) (d : D →ₜ* G)
    (τ φ : G) (h : ∀ U : OpenNormalSubgroup G, quotientGenerates i d U τ φ)
    (f : G →ₜ* P) :
    (∀ x : I, ∃ n : ℤ, f (i x) = f τ ^ n) ∧
    (∀ y : D, f (d y) ∈ Subgroup.closure ({f τ,f φ} : Set P)) := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.toMonoidHom.ker
      isOpen' := (isOpen_discrete ({1} : Set P)).preimage f.continuous
      isNormal' := inferInstance }
  let q := QuotientGroup.mk' (U : Subgroup G)
  have hk : q.ker ≤ f.toMonoidHom.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp hx
  refine ⟨?_,?_⟩
  · intro x
    obtain ⟨n,hn⟩ := (h U).1 x
    exact ⟨n,HomKernelTransfer.eq_zpow_of_eq_zpow q f.toMonoidHom hk hn⟩
  · intro y
    change f.toMonoidHom (d y) ∈ Subgroup.closure ({f.toMonoidHom τ,f.toMonoidHom φ} : Set P)
    have hy : q (d y) ∈ Subgroup.closure (q '' ({τ,φ} : Set G)) := by
      simpa only [Set.image_insert_eq,Set.image_singleton] using (h U).2 y
    simpa only [Set.image_insert_eq,Set.image_singleton] using
      HomKernelTransfer.mem_closure_image q f.toMonoidHom hk hy

end UnitDistance.ProfiniteTame
