module

public import UnitDistance.FilteredLinearInjection
public import UnitDistance.GroupAugmentationHilbertShift

@[expose] public section
set_option backward.privateInPublic true


/-!
# Strict coefficient injections from an elementary left inverse

Every left group-algebra-linear coefficient map preserves augmentation
powers. If a second such map is a left inverse after augmentation, their
error raises degree. Consequently the first map reflects every actual
augmentation power and is injective for finite 2-groups. This proves the
filtered coordinate injection used by the optimized relation-block argument.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq κ]

/-- The coordinate basis expansion for an actual left-algebra-linear map. -/
theorem coefficientLinearMap_apply
    (f : (κ → A R G) →ₗ[A R G] (ι → A R G)) (a : κ → A R G) :
    f a = ∑ j, a j • f (Pi.single j 1) := by
  classical
  have ha : a = ∑ j, a j • Pi.single j 1 := by
    ext k
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  calc
    f a = f (∑ j, a j • Pi.single j 1) := congrArg f ha
    _ = _ := by simp

/-- All actual left-algebra-linear coefficient maps preserve the right
ideal filtration on coefficients. -/
theorem coefficientLinearMap_filtered
    (f : (κ → A R G) →ₗ[A R G] (ι → A R G)) (n : ℕ) :
    (coefficientPower R G (ι := κ) n).map (f.restrictScalars R) ≤
      coefficientPower R G (ι := ι) n := by
  rintro a ⟨b,hb,rfl⟩
  apply (mem_coefficientPower R G n _).mpr
  intro i
  change f b i ∈ power R G n
  rw [coefficientLinearMap_apply R G f b]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Submodule.sum_mem
  intro j _
  exact mul_mem_right R G n _ _ ((mem_coefficientPower R G n b).mp hb j)

/-- A matrix with augmentation-zero entries raises every coefficient
augmentation degree by one. -/
theorem coefficientLinearMap_raises
    (f : (κ → A R G) →ₗ[A R G] (ι → A R G))
    (hf : ∀ j i, augmentation R G (f (Pi.single j 1) i) = 0)
    (n : ℕ) (a : κ → A R G) (ha : a ∈ coefficientPower R G n) :
    f a ∈ coefficientPower R G (n+1) := by
  apply (mem_coefficientPower R G (n+1) _).mpr
  intro i
  rw [coefficientLinearMap_apply R G f a]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Submodule.sum_mem
  intro j _
  exact mul_mem_succ R G ((mem_coefficientPower R G n a).mp ha j) (hf j i)

/-- An actual matrix left inverse in the elementary quotient makes the
coefficient injection strict at every augmentation degree. -/
theorem coefficientLinearMap_reflects
    (f : (κ → A R G) →ₗ[A R G] (ι → A R G))
    (r : (ι → A R G) →ₗ[A R G] (κ → A R G))
    (hleft : ∀ j k, augmentation R G (r (f (Pi.single j 1)) k) =
      augmentation R G ((Pi.single j (1 : A R G) : κ → A R G) k))
    (n : ℕ) (a : κ → A R G) (ha : f a ∈ coefficientPower R G n) :
    a ∈ coefficientPower R G n := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    have han : a ∈ coefficientPower R G n := ih ((mem_coefficientPower R G n _).mpr
      (fun i => power_succ_le R G n ((mem_coefficientPower R G (n+1) _).mp ha i)))
    have hrf : r (f a) ∈ coefficientPower R G (n+1) :=
      coefficientLinearMap_filtered R G r (n+1) ⟨f a,ha,rfl⟩
    let e := r.comp f - LinearMap.id
    have he : ∀ j k, augmentation R G (e (Pi.single j 1) k) = 0 := by
      intro j k
      change augmentation R G (r (f (Pi.single j 1)) k - (Pi.single j (1 : A R G) : κ → A R G) k) = 0
      rw [map_sub,hleft,sub_self]
    have he := coefficientLinearMap_raises R G e he n a han
    have hh := (coefficientPower R G (n+1)).sub_mem hrf he
    change r (f a) - (r (f a) - a) ∈ coefficientPower R G (n+1) at hh
    simpa only [sub_sub_cancel] using hh

variable [Finite G]
local notation "F" => ZMod 2

/-- A left inverse after augmentation proves actual injectivity over the
finite 2-group algebra, using proved augmentation nilpotence. -/
theorem coefficientLinearMap_injective (hG : IsPGroup 2 G)
    (f : (κ → A F G) →ₗ[A F G] (ι → A F G))
    (r : (ι → A F G) →ₗ[A F G] (κ → A F G))
    (hleft : ∀ j k, augmentation F G (r (f (Pi.single j 1)) k) =
      augmentation F G ((Pi.single j (1 : A F G) : κ → A F G) k)) : Function.Injective f := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro a ha
    have hfa : f a = 0 := ha
    have hm := coefficientLinearMap_reflects F G f r hleft (Nat.card G) a
      (by rw [hfa]; exact (coefficientPower F G (Nat.card G)).zero_mem)
    rwa [coefficientPower_bot G (Nat.card G) (power_card_eq_bot G 2 hG)] at hm
  · exact bot_le

/-- Actual elementary-injective coefficient maps preserve the Hilbert value
of every submodule with its induced shifted augmentation filtration. -/
theorem coefficientLinearMap_value_eq (hG : IsPGroup 2 G)
    (f : (κ → A F G) →ₗ[A F G] (ι → A F G))
    (r : (ι → A F G) →ₗ[A F G] (κ → A F G))
    (hleft : ∀ j k, augmentation F G (r (f (Pi.single j 1)) k) =
      augmentation F G ((Pi.single j (1 : A F G) : κ → A F G) k))
    (U : Submodule F (κ → A F G)) (N : ℕ) (t : ℝ) :
    FilteredHilbert.value F (ι → A F G)
      (fun n => U.map (f.restrictScalars F) ⊓ shiftedFoxCoefficientPower G n) N t =
    FilteredHilbert.value F (κ → A F G)
      (fun n => U ⊓ shiftedFoxCoefficientPower G n) N t := by
  have hf : Function.Injective (f.restrictScalars F) :=
    coefficientLinearMap_injective G hG f r hleft
  have hs (n : ℕ) : (U ⊓ shiftedFoxCoefficientPower G n).map (f.restrictScalars F) =
      U.map (f.restrictScalars F) ⊓ shiftedFoxCoefficientPower G n := by
    apply FilteredLinear.map_inf_eq F (κ → A F G) (ι → A F G)
      (shiftedFoxCoefficientPower G) (shiftedFoxCoefficientPower G) (f.restrictScalars F)
    · intro m
      exact coefficientLinearMap_filtered F G f (m-1)
    · intro m a ha
      exact coefficientLinearMap_reflects F G f r hleft (m-1) a ha
  have he := FilteredHilbert.value_map_add_kernel F (κ → A F G) (ι → A F G)
    (fun n => U ⊓ shiftedFoxCoefficientPower G n) (f.restrictScalars F) N t
  simp only [hs,LinearMap.ker_eq_bot.mpr hf,inf_bot_eq] at he
  simpa only [FilteredHilbert.value,finrank_bot,Nat.cast_zero,sub_self,zero_mul,
    Finset.sum_const_zero,add_zero] using he

end UnitDistance.GroupAugmentation
