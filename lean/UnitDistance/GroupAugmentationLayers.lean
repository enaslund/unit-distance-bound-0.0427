module

public import UnitDistance.GroupAugmentation
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.CharP.Two

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual dimension layers and the low-layer compatibility criterion

The layer maps below are quotient-group homomorphisms induced by a genuine
group homomorphism. Their injectivity is equivalent to an ordinary kernel
condition. For a local group with third dimension subgroup trivial,
injectivity of the first two such maps forces compatibility in every degree.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]

/-- Commutators have the sum of the two augmentation degrees. -/
theorem commutator_mem {m n : ℕ} {g h : G}
    (hg : g ∈ dimensionSubgroup R G m) (hh : h ∈ dimensionSubgroup R G n) :
    g * h * g⁻¹ * h⁻¹ ∈ dimensionSubgroup R G (m+n) := by
  have ha := mul_mem_add R G hg hh
  have hb := mul_mem_add R G hh hg
  rw [Nat.add_comm n m] at hb
  have hc := (power R G (m+n)).sub_mem ha hb
  have hd := mul_mem_right R G (m+n) _ (delta R g⁻¹) hc
  have he := mul_mem_right R G (m+n) _ (delta R h⁻¹) hd
  have hid : ((delta R g - 1) * (delta R h - 1) -
      (delta R h - 1) * (delta R g - 1)) * delta R g⁻¹ * delta R h⁻¹ =
      delta R (g*h*g⁻¹*h⁻¹) - 1 := by
    have ht : (delta R g - 1) * (delta R h - 1) -
        (delta R h - 1) * (delta R g - 1) = delta R g * delta R h - delta R h * delta R g := by
      noncomm_ring
    rw [ht]
    simp [sub_mul, mul_assoc]
  simpa only [hid, mem_dimensionSubgroup] using he

/-- In characteristic two, squaring doubles augmentation degree. -/
theorem square_mem [CharP R 2] {n : ℕ} {g : G}
    (hg : g ∈ dimensionSubgroup R G n) :
    g^2 ∈ dimensionSubgroup R G (2*n) := by
  have h := mul_mem_add R G hg hg
  have hid : (delta R g - 1) * (delta R g - 1) = delta R (g^2) - 1 := by
    have hs : delta R g + delta R g = 0 := by
      ext x
      simp [CharTwo.add_self_eq_zero]
    have hn : -(1 : A R G) = 1 := by
      ext x
      simp [CharTwo.neg_eq]
    calc
      (delta R g - 1) * (delta R g - 1) =
          delta R g * delta R g - (delta R g + delta R g) + 1 := by noncomm_ring
      _ = delta R (g^2) - 1 := by simp [hs, sub_eq_add_neg, hn, pow_two]
  change delta R (g^2) - 1 ∈ power R G (2*n)
  simpa only [hid, two_mul] using h

/-- The denominator of the n-th dimension layer, as a subgroup of its numerator. -/
def layerDenominator (n : ℕ) : Subgroup (dimensionSubgroup R G n) :=
  (dimensionSubgroup R G (n+1)).comap (dimensionSubgroup R G n).subtype

instance layerDenominator_normal (n : ℕ) : (layerDenominator R G n).Normal :=
  Subgroup.Normal.comap (dimensionSubgroup_normal R G (n+1)) _

abbrev Layer (n : ℕ) := (dimensionSubgroup R G n) ⧸ layerDenominator R G n

variable {H : Type*} [Group H]

/-- Restriction of a genuine group homomorphism to the n-th dimension subgroup. -/
def dimensionHom (f : G →* H) (n : ℕ) :
    dimensionSubgroup R G n →* dimensionSubgroup R H n :=
  (f.comp (dimensionSubgroup R G n).subtype).codRestrict _ (fun g =>
    map_dimensionSubgroup_le R G f n ⟨g, g.property, rfl⟩)

@[simp] theorem dimensionHom_apply (f : G →* H) (n : ℕ)
    (g : dimensionSubgroup R G n) : (dimensionHom R G f n g : H) = f g := rfl

/-- The actual induced group homomorphism on successive dimension layers. -/
def layerMap (f : G →* H) (n : ℕ) : Layer R G n →* Layer R H n :=
  QuotientGroup.map (layerDenominator R G n) (layerDenominator R H n)
    (dimensionHom R G f n) (by
      intro g hg
      exact map_dimensionSubgroup_le R G f (n+1) ⟨g, hg, rfl⟩)

@[simp] theorem layerMap_mk (f : G →* H) (n : ℕ) (g : dimensionSubgroup R G n) :
    layerMap R G f n (QuotientGroup.mk g) = QuotientGroup.mk (dimensionHom R G f n g) := rfl

/-- This is precisely injectivity on the actual quotient layer, expressed
as the absence of new kernel elements in the next ambient dimension subgroup. -/
theorem layerMap_injective_iff (f : G →* H) (n : ℕ) :
    Function.Injective (layerMap R G f n) ↔
      ∀ g ∈ dimensionSubgroup R G n,
        f g ∈ dimensionSubgroup R H (n+1) → g ∈ dimensionSubgroup R G (n+1) := by
  constructor
  · intro hinj g hg hfg
    have he : layerMap R G f n (QuotientGroup.mk (⟨g,hg⟩ : dimensionSubgroup R G n)) = 1 := by
      rw [layerMap_mk, QuotientGroup.eq_one_iff]
      exact hfg
    have hz := hinj (he.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff (⟨g,hg⟩ : dimensionSubgroup R G n)).mp hz
  · intro h
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_bot_iff.mp
    intro x hx
    induction x using Quotient.inductionOn with
    | h g =>
      change layerMap R G f n (QuotientGroup.mk g) = 1 at hx
      rw [layerMap_mk, QuotientGroup.eq_one_iff] at hx
      change QuotientGroup.mk g = 1
      rw [QuotientGroup.eq_one_iff]
      exact h g g.property hx

/-- If the local third dimension subgroup vanishes, injection of the first
two actual layers forces pullback equality of every dimension subgroup.
In particular this applies to the specified dyadic group, without any
assumed equality of higher filtrations. -/
theorem comap_dimensionSubgroup_eq_of_first_two_layers
    (f : G →* H) (hthird : dimensionSubgroup R G 3 = ⊥)
    (hfirst : Function.Injective (layerMap R G f 1))
    (hsecond : Function.Injective (layerMap R G f 2)) (n : ℕ) :
    (dimensionSubgroup R H n).comap f = dimensionSubgroup R G n := by
  apply le_antisymm
  · intro g hg
    rcases n with _ | _ | n
    · simp
    · simp
    rcases n with _ | n
    · exact (layerMap_injective_iff R G f 1).mp hfirst g (by simp) hg
    · have hg3 : f g ∈ dimensionSubgroup R H 3 :=
        dimensionSubgroup_antitone R H (by omega : 3 ≤ n+3) hg
      have hg2 : g ∈ dimensionSubgroup R G 2 :=
        (layerMap_injective_iff R G f 1).mp hfirst g (by simp)
          (dimensionSubgroup_antitone R H (by omega : 2 ≤ 3) hg3)
      have hg3' := (layerMap_injective_iff R G f 2).mp hsecond g hg2 hg3
      rw [hthird, Subgroup.mem_bot] at hg3'
      subst g
      exact Subgroup.one_mem _
  · intro g hg
    exact map_dimensionSubgroup_le R G f n ⟨g,hg,rfl⟩

end UnitDistance.GroupAugmentation
