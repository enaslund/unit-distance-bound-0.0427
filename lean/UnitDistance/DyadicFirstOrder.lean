module

public import UnitDistance.GroupAugmentationMoments
public import UnitDistance.GroupAugmentationDyadic
public import UnitDistance.DyadicFinal

@[expose] public section
set_option backward.privateInPublic true


/-! The actual first-order quotient of the dyadic group algebra is detected
by its augmentation and its three genuine genus-character moments. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace UnitDistance.Dyadic.FirstOrder
open GroupAugmentation
abbrev V := Fin 3 → F

def character (i : Fin 3) : D →* Multiplicative F where
  toFun g := Multiplicative.ofAdd (![g.a,g.b,parity g.c] i)
  map_one' := by fin_cases i <;> rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    fin_cases i
    · rfl
    · rfl
    · exact map_add parity g.c h.c

theorem character_gen (i j : Fin 3) :
    (character j (Filtration.gen i)).toAdd=(Pi.single i 1 : V) j := by
  have h : ∀i j : Fin 3,(character j (Filtration.gen i)).toAdd=(Pi.single i 1 : V) j := by decide +kernel
  exact h i j

def coordinates : AlgebraD →ₗ[F] (Fin 4 → F) :=
  LinearMap.pi (Fin.cases (augmentation F D).toLinearMap (fun i => moment (character i)))

@[simp] theorem coordinates_zero (a : AlgebraD) : coordinates a 0=augmentation F D a := rfl
@[simp] theorem coordinates_succ (a : AlgebraD) (i : Fin 3) :
    coordinates a i.succ=moment (character i) a := rfl

def sectionColumn : Fin 4 → AlgebraD :=
  Fin.cases 1 (fun i => delta F (Filtration.gen i)-1)

theorem coordinates_column (i j : Fin 4) :
    coordinates (sectionColumn i) j=(Pi.single i 1 : Fin 4 → F) j := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [sectionColumn,dyadic_augmentation]
    · simp [sectionColumn,dyadic_augmentation]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [sectionColumn,dyadic_augmentation]
    · simp only [sectionColumn,Fin.cases_succ,coordinates_succ,map_sub,moment_delta,moment_one,sub_zero,
        character_gen]
      simp [Pi.single_apply]

theorem coordinates_surjective : Function.Surjective coordinates := by
  intro v
  refine ⟨∑i,v i • sectionColumn i,?_⟩
  ext j
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,coordinates_column]
  simp [Pi.single_apply]

theorem power_two_le_ker : power F D 2≤coordinates.ker := by
  intro a ha
  apply LinearMap.mem_ker.mpr
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h := power_antitone F D (by decide : 1≤2) ha
    rw [power_one] at h
    exact h
  · exact moment_power_two (character j) a ha

/-- Exact equality of actual subspaces, using the already certified dimension28. -/
theorem ker_coordinates : coordinates.ker=AlgebraD.augmentationPower 2 := by
  have hdim : Module.finrank F coordinates.ker=28 := by
    have h := LinearMap.finrank_range_add_finrank_ker coordinates
    have hr : Module.finrank F coordinates.range=4 := by
      rw [LinearMap.range_eq_top.mpr coordinates_surjective,finrank_top]
      simp
    have ha : Module.finrank F AlgebraD=32 := by
      simpa using AlgebraD.finrank_algebra
    omega
  apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [←dyadic_power]
    exact power_two_le_ker
  · rw [hdim]
    exact AlgebraD.augmentation_dimensions 2

/-- The four moments are a complete test for second augmentation power. -/
theorem mem_power_two_iff (a : AlgebraD) :
    a∈AlgebraD.augmentationPower 2 ↔ augmentation F D a=0 ∧
      ∀i : Fin 3,moment (character i) a=0 := by
  rw [←ker_coordinates,LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨congrFun h 0,fun i=>congrFun h i.succ⟩
  · rintro ⟨h0,h1⟩
    funext i
    exact Fin.cases h0 h1 i

end UnitDistance.Dyadic.FirstOrder
