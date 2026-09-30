module

public import UnitDistance.JenningsAdaptedProduct
public import UnitDistance.GroupAugmentationProductBasis
public import UnitDistance.GroupAugmentationStrictness

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual filtered local freeness for finite 2-groups

For an actual homomorphism of finite 2-groups whose actual dimension-layer
maps are injective, the ambient group algebra is the direct sum of shifted
copies of the local group algebra. The shifts are actual complementary
augmentation-monomial weights. Multiplication and every actual augmentation
power are respected, without an assumed Jennings or adapted-basis theorem.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (D P : Type*) [Group D] [Group P] [Finite D] [Finite P]
variable (f : D →* P)
variable (hinj : ∀ n, Function.Injective (layerMap (ZMod 2) D f n))
variable (hD : IsPGroup 2 D) (hP : IsPGroup 2 P)

/-- Actual right-module coordinates in the constructed augmentation basis. -/
def filteredCoordinates : A (ZMod 2) P ≃ₗ[ZMod 2]
    (ComplementChoices D P f hinj →₀ A (ZMod 2) D) :=
  productCoordinates (ZMod 2) D P _ _ (generatorBasis D hD)
    (adaptedProductBasis D P f hinj hD hP)

/-- Every complementary monomial gives exactly one whole local summand. -/
theorem filteredCoordinates_block (t : ComplementChoices D P f hinj) (a : A (ZMod 2) D) :
    filteredCoordinates D P f hinj hD hP
      (complementMonomial D P f hinj t * induced (ZMod 2) D f a) = Finsupp.single t a :=
  productCoordinates_block (ZMod 2) D P _ _ (generatorBasis D hD)
    (adaptedProductBasis D P f hinj hD hP) f (complementMonomial D P f hinj)
    (adaptedProductBasis_apply D P f hinj hD hP) t a

/-- The actual decomposition is right linear over the original local
group algebra, including all higher-order coefficients. -/
theorem filteredCoordinates_mul (a : A (ZMod 2) P) (b : A (ZMod 2) D)
    (t : ComplementChoices D P f hinj) :
    filteredCoordinates D P f hinj hD hP (a * induced (ZMod 2) D f b) t =
      filteredCoordinates D P f hinj hD hP a t * b :=
  productCoordinates_mul (ZMod 2) D P _ _ (generatorBasis D hD)
    (adaptedProductBasis D P f hinj hD hP) f (complementMonomial D P f hinj)
    (adaptedProductBasis_apply D P f hinj hD hP) a b t

/-- The exact all-degree filtered local freeness assertion. The shifts are
nonnegative actual complementary weights, and both sides use actual powers. -/
theorem filteredCoordinates_mem_power_iff (a : A (ZMod 2) P) (n : ℕ) :
    a ∈ power (ZMod 2) P n ↔ ∀ t,
      filteredCoordinates D P f hinj hD hP a t ∈
        power (ZMod 2) D (n-complementWeight D P f hinj hP t) :=
  productCoordinates_mem_power_iff (ZMod 2) D P _ _ (generatorBasis D hD)
    (adaptedProductBasis D P f hinj hD hP)
    (complementWeight D P f hinj hP) (generatorWeight D hD)
    (generatorWeightedSpan_eq_power D hD)
    (adaptedProductWeightedSpan_eq_power D P f hinj hD hP) a n

/-- Actual ambient powers are carried onto the direct sums of shifted
actual local powers, rather than merely included in them. -/
theorem filteredCoordinates_map_power (n : ℕ) :
    (power (ZMod 2) P n).map (filteredCoordinates D P f hinj hD hP).toLinearMap =
      shiftedCoefficientPower (ZMod 2) D (ComplementChoices D P f hinj)
        (complementWeight D P f hinj hP) n :=
  map_power_productCoordinates (ZMod 2) D P _ _ (generatorBasis D hD)
    (adaptedProductBasis D P f hinj hD hP)
    (complementWeight D P f hinj hP) (generatorWeight D hD)
    (generatorWeightedSpan_eq_power D hD)
    (adaptedProductWeightedSpan_eq_power D P f hinj hD hP) n

/-- Every actual common row annihilator is detected on the actual local
coordinates under this filtered right-module decomposition. -/
theorem filteredCoordinates_annihilator_iff {ι : Type*} (a : A (ZMod 2) P)
    (c : ι → A (ZMod 2) D) :
    (∀ i, a * induced (ZMod 2) D f (c i) = 0) ↔
      ∀ t i, filteredCoordinates D P f hinj hD hP a t * c i = 0 := by
  constructor
  · intro h t i
    rw [← filteredCoordinates_mul,h i,map_zero]
    rfl
  · intro h i
    apply (filteredCoordinates D P f hinj hD hP).injective
    apply Finsupp.ext
    intro t
    simp only [map_zero,Finsupp.zero_apply]
    rw [filteredCoordinates_mul]
    exact h t i

end UnitDistance.GroupAugmentation
