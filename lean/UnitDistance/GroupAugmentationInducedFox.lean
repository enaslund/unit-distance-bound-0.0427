module

public import UnitDistance.GroupAugmentationFilteredRows

@[expose] public section
set_option backward.privateInPublic true


/-!
# Strict induction of the full actual local augmentation map

The actual filtered right-module coordinates identify the ambient image of
local generator differences, and lift every vector in its induced filtration
with exactly the required coefficient degree. This applies to the complete
local augmentation kernel, beyond induction of one prescribed Fox row.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (R D P T : Type*) [CommRing R] [Group D] [Group P] [Fintype T]
variable {ι : Type*} [Fintype ι]
variable (f : D →* P) (e : A R P ≃ₗ[R] (T →₀ A R D)) (w : T → ℕ)
variable (hmul : ∀ a b t, e (a*induced R D f b) t = e a t*b)
variable (hpower : ∀ a n, a ∈ power R P n ↔ ∀ t, e a t ∈ power R D (n-w t))
variable (generators : ι → D)

include hmul in
/-- Actual right-module coordinates commute with the full augmentation
map attached to the local generators. -/
theorem induced_foxMap_coordinates (a : ι → A R P) (t : T) :
    e (foxMap R P (fun i => f (generators i)) a) t =
      foxMap R D generators (fun i => e (a i) t) := by
  change e (∑ i, a i*(delta R (f (generators i))-1)) t =
    ∑ i, e (a i) t*(delta R (generators i)-1)
  rw [map_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hd : delta R (f (generators i))-1 = induced R D f (delta R (generators i)-1) := by simp
  rw [hd,hmul]

variable (hgen : Subgroup.closure (Set.range generators) = ⊤)

include hmul hpower hgen in
/-- An actual coordinatewise local augmentation preimage reconstructs to
an ambient preimage with the prescribed actual coefficient degree. -/
theorem induced_foxMap_preimage (n : ℕ) (a : A R P)
    (ha : ∀ t, e a t ∈ power R D ((n-w t)+1)) :
    ∃ b ∈ coefficientPower R P (ι := ι) n,
      foxMap R P (fun i => f (generators i)) b = a := by
  classical
  have hc : ∀ t, ∃ b ∈ coefficientPower R D (ι := ι) (n-w t),
      foxMap R D generators b = e a t := by
    intro t
    have ht := ha t
    rw [← foxMap_strict R D generators hgen] at ht
    exact ht
  choose b hb he using hc
  let v : ι → A R P := fun i => e.symm (Finsupp.equivFunOnFinite.symm (fun t => b t i))
  have hv (i : ι) (t : T) : e (v i) t = b t i := by simp [v]
  refine ⟨v,(mem_coefficientPower R P n v).mpr ?_,?_⟩
  · intro i
    apply (hpower (v i) n).mpr
    intro t
    rw [hv]
    exact (mem_coefficientPower R D _ _).mp (hb t) i
  · apply e.injective
    apply Finsupp.ext
    intro t
    rw [induced_foxMap_coordinates R D P T f e hmul generators]
    simp_rw [hv]
    exact he t

include hmul hpower hgen in
/-- The actual ambient local augmentation image consists exactly of the
coordinate blocks lying in the actual local augmentation ideal. -/
theorem induced_foxMap_mem_range_iff (a : A R P) :
    a ∈ (foxMap R P (fun i => f (generators i))).range ↔
      ∀ t, e a t ∈ power R D 1 := by
  constructor
  · rintro ⟨b,rfl⟩ t
    rw [induced_foxMap_coordinates R D P T f e hmul generators]
    rw [← foxMap_strict R D generators hgen 0]
    exact ⟨_,(mem_coefficientPower R D 0 _).mpr (fun _ => by trivial),rfl⟩
  · intro ha
    obtain ⟨b,_,hb⟩ := induced_foxMap_preimage R D P T f e w hmul hpower generators hgen 0 a
      (by simpa using ha)
    exact ⟨b,hb⟩

include hmul hpower hgen in
/-- The full induced local augmentation map is strict in every actual
augmentation degree. -/
theorem induced_foxMap_strict (n : ℕ) :
    (coefficientPower R P (ι := ι) n).map (foxMap R P (fun i => f (generators i))) =
      (foxMap R P (fun i => f (generators i))).range ⊓ power R P (n+1) := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    refine ⟨⟨b,rfl⟩,?_⟩
    change (∑ i, b i*(delta R (f (generators i))-1)) ∈ power R P (n+1)
    apply Submodule.sum_mem
    intro i _
    exact mul_mem_succ R P ((mem_coefficientPower R P _ _).mp hb i) (by simp)
  · rintro ⟨ha,hap⟩
    apply induced_foxMap_preimage R D P T f e w hmul hpower generators hgen n a
    intro t
    by_cases ht : n < w t
    · simpa only [Nat.sub_eq_zero_of_le (Nat.le_of_lt ht),zero_add] using
        (induced_foxMap_mem_range_iff R D P T f e w hmul hpower generators hgen a).mp ha t
    · have hh := (hpower a (n+1)).mp hap t
      have he : (n+1)-w t = (n-w t)+1 := by omega
      rwa [he] at hh

end UnitDistance.GroupAugmentation
