module

public import UnitDistance.JenningsOrderedBasis

@[expose] public section
set_option backward.privateInPublic true


/-! Homogeneous spanning follows from generation of the actual dimension
subgroups by directions of the appropriate weights. -/
noncomputable section
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]

theorem initial_difference_of_mem_closure (n : ℕ) (hn : 1≤n)
    (S : Set G) (H : Submodule R (A R G))
    (hS : ∀ g∈S, g∈dimensionSubgroup R G n ∧
      ∃ b∈H, delta R g-1-b∈power R G (n+1))
    {g : G} (hg : g∈Subgroup.closure S) :
    g∈dimensionSubgroup R G n ∧ ∃ b∈H, delta R g-1-b∈power R G (n+1) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact ⟨Subgroup.one_mem _,0,H.zero_mem,by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨hxn,b,hb,he⟩ := ihx
    obtain ⟨hyn,c,hc,hf⟩ := ihy
    refine ⟨Subgroup.mul_mem _ hxn hyn,b+c,H.add_mem hb hc,?_⟩
    have hm := power_antitone R G (show n+1≤n+n by omega) (mul_mem_add R G hxn hyn)
    have hid : delta R (x*y)-1-(b+c)=
        (delta R x-1-b)+(delta R y-1-c)+(delta R x-1)*(delta R y-1) := by
      rw [←delta_mul]
      noncomm_ring
    rw [hid]
    exact (power R G (n+1)).add_mem ((power R G (n+1)).add_mem he hf) hm
  | inv x hx ih =>
    obtain ⟨hxn,b,hb,he⟩ := ih
    have hxi := Subgroup.inv_mem (dimensionSubgroup R G n) hxn
    refine ⟨hxi,-b,H.neg_mem hb,?_⟩
    have hm := power_antitone R G (show n+1≤n+n by omega) (mul_mem_add R G hxn hxi)
    have hid : delta R x⁻¹-1-(-b)=
        -(delta R x-1-b)-(delta R x-1)*(delta R x⁻¹-1) := by
      have hm : delta R x*delta R x⁻¹=1 := by simp
      noncomm_ring [hm]
    rw [hid]
    exact (power R G (n+1)).sub_mem ((power R G (n+1)).neg_mem he) hm

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

theorem spansActualLayers_of_generation (g : ι → G) (w : ι → ℕ)
    (hg : ∀ i, g i∈dimensionSubgroup (ZMod 2) G (w i))
    (hgen : ∀ n, 1≤n → dimensionSubgroup (ZMod 2) G n≤
      Subgroup.closure {x | ∃ i, n≤w i ∧ x=g i}) :
    SpansActualLayers G ι g w := by
  intro n hn a
  apply (initial_difference_of_mem_closure (ZMod 2) G n hn
    {x | ∃ i, n≤w i ∧ x=g i}
    (JenningsCollection.homogeneousLinearSpan (ZMod 2) G ι
      (fun i ↦ delta (ZMod 2) (g i)-1) w n) ?_ (hgen n hn a.property)).2
  rintro x ⟨i,hi,rfl⟩
  refine ⟨dimensionSubgroup_antitone (ZMod 2) G hi (hg i),?_⟩
  by_cases he : w i=n
  · refine ⟨delta (ZMod 2) (g i)-1,Submodule.subset_span ⟨i,he,rfl⟩,?_⟩
    simp
  · exact ⟨0,Submodule.zero_mem _,by
      simpa only [sub_zero] using power_antitone (ZMod 2) G
        (show n+1≤w i by omega) (hg i)⟩

end UnitDistance.GroupAugmentation
