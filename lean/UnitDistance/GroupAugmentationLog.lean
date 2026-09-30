module

public import UnitDistance.GroupAugmentationLayers

@[expose] public section
set_option backward.privateInPublic true


/-!
# Injecting actual dimension layers into the augmentation quotients

For positive degree, `g ↦ g-1 mod Iⁿ⁺¹` is a group homomorphism from
`Dₙ(G)` to the additive group of the actual algebra quotient. Its kernel is
exactly `Dₙ₊₁(G)`. The resulting injection gives a concrete algebraic way to
verify the layer-injectivity hypotheses, with a naturality statement for
actual group homomorphisms.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]

/-- The ordinary algebra quotient at the next augmentation degree. -/
abbrev AugmentationQuotient (n : ℕ) := A R G ⧸ power R G (n+1)

/-- The group difference viewed in the actual quotient algebra. -/
def differenceHom (n : ℕ) (hn : 1 ≤ n) :
    dimensionSubgroup R G n →* Multiplicative (AugmentationQuotient R G n) where
  toFun g := Multiplicative.ofAdd ((power R G (n+1)).mkQ (delta R (g : G)-1))
  map_one' := by simp
  map_mul' g h := by
    change (power R G (n+1)).mkQ (delta R ((g : G)*(h : G))-1) =
      (power R G (n+1)).mkQ (delta R (g : G)-1) +
      (power R G (n+1)).mkQ (delta R (h : G)-1)
    rw [← map_add]
    apply (Submodule.Quotient.eq _).mpr
    have hm := mul_mem_add R G g.property h.property
    have hd : delta R ((g : G)*(h : G))-1 -
        ((delta R (g : G)-1)+(delta R (h : G)-1)) =
        (delta R (g : G)-1)*(delta R (h : G)-1) := by
      rw [← delta_mul]
      noncomm_ring
    rw [hd]
    exact power_antitone R G (by omega : n+1 ≤ n+n) hm

@[simp] theorem differenceHom_eq_one_iff (n : ℕ) (hn : 1 ≤ n)
    (g : dimensionSubgroup R G n) :
    differenceHom R G n hn g = 1 ↔ g ∈ layerDenominator R G n := by
  change (power R G (n+1)).mkQ (delta R (g : G)-1) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

theorem differenceHom_ker (n : ℕ) (hn : 1 ≤ n) :
    (differenceHom R G n hn).ker = layerDenominator R G n := by
  ext g
  exact differenceHom_eq_one_iff R G n hn g

/-- The faithful group-layer realization in the actual augmentation quotient. -/
def layerEmbedding (n : ℕ) (hn : 1 ≤ n) :
    Layer R G n →* Multiplicative (AugmentationQuotient R G n) :=
  QuotientGroup.lift (layerDenominator R G n) (differenceHom R G n hn)
    (by rw [differenceHom_ker])

theorem layerEmbedding_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (layerEmbedding R G n hn) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (differenceHom_ker R G n hn).symm

variable {H : Type*} [Group H]

/-- The induced linear map on the ordinary augmentation quotients. -/
def quotientMap (f : G →* H) (n : ℕ) :
    AugmentationQuotient R G n →ₗ[R] AugmentationQuotient R H n :=
  (power R G (n+1)).mapQ (power R H (n+1)) (induced R G f).toLinearMap
    (fun a ha => induced_mem_power R G f (n+1) a ha)

@[simp] theorem quotientMap_mk (f : G →* H) (n : ℕ) (a : A R G) :
    quotientMap R G f n ((power R G (n+1)).mkQ a) =
      (power R H (n+1)).mkQ (induced R G f a) := rfl

/-- Naturality of the concrete group-difference injection. -/
theorem differenceHom_natural (f : G →* H) (n : ℕ) (hn : 1 ≤ n)
    (g : dimensionSubgroup R G n) :
    quotientMap R G f n (Multiplicative.toAdd (differenceHom R G n hn g)) =
      Multiplicative.toAdd (differenceHom R H n hn (dimensionHom R G f n g)) := by
  change (power R H (n+1)).mkQ (induced R G f (delta R (g : G)-1)) =
    (power R H (n+1)).mkQ (delta R (f g)-1)
  simp

/-- To verify a group-layer injection it suffices to check the actual
linear quotient map on the independently defined group-difference images.
This does not postulate injectivity of the full ambient algebra quotient. -/
theorem layerMap_injective_of_difference_detection
    (f : G →* H) (n : ℕ) (hn : 1 ≤ n)
    (hdetect : ∀ g : dimensionSubgroup R G n,
      quotientMap R G f n (Multiplicative.toAdd (differenceHom R G n hn g)) = 0 →
        Multiplicative.toAdd (differenceHom R G n hn g) = 0) :
    Function.Injective (layerMap R G f n) := by
  apply (layerMap_injective_iff R G f n).mpr
  intro g hg hfg
  let x : dimensionSubgroup R G n := ⟨g,hg⟩
  have ht : quotientMap R G f n (Multiplicative.toAdd (differenceHom R G n hn x)) = 0 := by
    rw [differenceHom_natural]
    change (power R H (n+1)).mkQ (delta R (f g)-1) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hfg
  have hzero := hdetect x ht
  exact (Submodule.Quotient.mk_eq_zero _).mp hzero

end UnitDistance.GroupAugmentation
