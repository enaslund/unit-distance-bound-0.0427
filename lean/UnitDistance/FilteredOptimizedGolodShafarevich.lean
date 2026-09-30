module

public import UnitDistance.JenningsGlobalKernelCost
public import UnitDistance.GroupAugmentationGlobalCommonRow

@[expose] public section
set_option backward.privateInPublic true


/-!
# Global optimized finite Golod--Shafarevich obstruction

Actual global subspaces span the actual augmentation kernel; an actual
common subspace is subtracted once. Specialization to the mapped dyadic
kernel and row uses their proved values and actual coordinate maps. The
arithmetic construction of these global blocks remains a separate input.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open FilteredHilbert
variable (P : Type*) [Group P] [Finite P] (hP : IsPGroup 2 P)
local notation "F" => ZMod 2
variable {ι J : Type*} [Fintype ι] [Fintype J]
variable (generators : ι → P)

include hP in
/-- The global block inequality subtracts an actual common subspace from
actual induced Hilbert values. All spans and inclusions are ordinary
subspaces of the actual global Fox coefficient module. -/
theorem finite_fox_block_inequality
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (blocks : J → Submodule F (ι → A F P))
    (dyadic common : Submodule F (ι → A F P))
    (hspan : (foxMap F P generators).ker = (⨆ j, blocks j) ⊔ dyadic)
    (hcommon : common ≤ (⨆ j, blocks j) ⊓ dyadic)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ (1-(Fintype.card ι : ℝ)*t)*
        Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) +
      (∑ j, value F (ι → A F P)
        (fun n => blocks j ⊓ shiftedFoxCoefficientPower P n) (Nat.card P+1) t) +
      value F (ι → A F P)
        (fun n => dyadic ⊓ shiftedFoxCoefficientPower P n) (Nat.card P+1) t -
      value F (ι → A F P)
        (fun n => common ⊓ shiftedFoxCoefficientPower P n) (Nat.card P+1) t := by
  have hN := shiftedFoxCoefficientPower_nilpotent P (ι := ι) hP (Nat.card P+1) le_rfl
  have hi := value_sup_add_inf_le F (ι → A F P) (shiftedFoxCoefficientPower P)
    (shiftedFoxCoefficientPower_zero P) (⨆ j, blocks j) dyadic (Nat.card P+1) hN t ht0 ht1
  have hc := value_induced_mono F (ι → A F P) (shiftedFoxCoefficientPower P)
    (shiftedFoxCoefficientPower_antitone P) common ((⨆ j, blocks j) ⊓ dyadic)
    hcommon (Nat.card P+1) t ht0
  have hb := value_iSup_le F (ι → A F P) (shiftedFoxCoefficientPower P)
    (shiftedFoxCoefficientPower_antitone P) (shiftedFoxCoefficientPower_zero P)
    blocks (Nat.card P+1) hN t ht0 ht1
  rw [← hspan] at hi
  have hk : (fun n => (foxMap F P generators).ker ⊓ shiftedFoxCoefficientPower P n) =
      foxKernelPower P generators := by funext n; exact inf_comm _ _
  rw [hk,value_foxKernel P generators hgen hP t] at hi
  linarith

include hP in
/-- The actual dyadic cost and actual common-row correction in global
coordinates give the optimized dyadic contribution. The other blocks retain
their actual Hilbert values, so no assigned cost conceals a structural input. -/
theorem finite_optimized_dyadic_block_inequality
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (blocks : J → Submodule F (ι → A F P))
    (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
    (hwords : ∀ j, FreeGroup.lift generators (words j) = f (Dyadic.Filtration.gen j))
    (hfirst : Function.Injective (layerMap F Dyadic.D f 1))
    (hsecond : Function.Injective (layerMap F Dyadic.D f 2))
    (r : (ι → A F P) →ₗ[A F P] (Fin 3 → A F P))
    (hleft : ∀ j k, augmentation F P
        (r (foxSubstitutionAlgebra F P generators words (Pi.single j 1)) k) =
      augmentation F P ((Pi.single j (1 : A F P) : Fin 3 → A F P) k))
    (c : Fin 3 → Dyadic.AlgebraD)
    (hc : ∀ i, c i-Dyadic.AlgebraD.linearFoxCoefficients i ∈ Dyadic.AlgebraD.augmentationPower 2)
    (hspan : (foxMap F P generators).ker =
      (⨆ j, blocks j) ⊔ globalFoxBlock P generators words)
    (hrow : foxMap F P (fun j => FreeGroup.lift generators (words j))
      (fun i => induced F Dyadic.D f (c i)) = 0)
    (hcommon : globalDyadicRow P generators words f c ≤ ⨆ j, blocks j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ (1-(Fintype.card ι : ℝ)*t + (3*t-1+1/((1+t)^3*(1+t^2)^2)) -
        t^2*(1-t^7/((1+t)^3*(1+t^2)^2)))*
        Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) +
      ∑ j, value F (ι → A F P)
        (fun n => blocks j ⊓ shiftedFoxCoefficientPower P n) (Nat.card P+1) t := by
  have hi := finite_fox_block_inequality P hP generators hgen blocks
    (globalFoxBlock P generators words) (globalDyadicRow P generators words f c) hspan
    (le_inf hcommon (globalDyadicRow_le_block P generators words f c hrow)) t ht0 ht1
  rw [global_dyadic_row_cost P generators hP words f hfirst hsecond r hleft c hc t ht0] at hi
  have hb := global_dyadic_block_cost P generators hP words f hwords hfirst hsecond t ht0 ht1
  nlinarith

include hP in
/-- All other local blocks can be charged by their independently defined
actual local Hilbert polynomials. Together with the proved dyadic correction,
this is the optimized relation-block inequality for an arbitrary genuine
finite realization of the local-to-global data. -/
theorem finite_optimized_local_family_inequality
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (D : J → Type*) [∀ j, Group (D j)] [∀ j, Finite (D j)]
    (κ : J → Type*) [∀ j, Fintype (κ j)]
    (localGenerators : ∀ j, κ j → D j)
    (localMaps : ∀ j, D j →* P)
    (localWords : ∀ j, κ j → FreeGroup ι)
    (hlocalTwo : ∀ j, IsPGroup 2 (D j))
    (hlocalGen : ∀ j, Subgroup.closure (Set.range (localGenerators j)) = ⊤)
    (hlocalWords : ∀ j i, FreeGroup.lift generators (localWords j i) =
      localMaps j (localGenerators j i))
    (hlayers : ∀ j n, Function.Injective (layerMap F (D j) (localMaps j) n))
    (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
    (hwords : ∀ j, FreeGroup.lift generators (words j) = f (Dyadic.Filtration.gen j))
    (hfirst : Function.Injective (layerMap F Dyadic.D f 1))
    (hsecond : Function.Injective (layerMap F Dyadic.D f 2))
    (r : (ι → A F P) →ₗ[A F P] (Fin 3 → A F P))
    (hleft : ∀ j k, augmentation F P
        (r (foxSubstitutionAlgebra F P generators words (Pi.single j 1)) k) =
      augmentation F P ((Pi.single j (1 : A F P) : Fin 3 → A F P) k))
    (c : Fin 3 → Dyadic.AlgebraD)
    (hc : ∀ i, c i-Dyadic.AlgebraD.linearFoxCoefficients i ∈ Dyadic.AlgebraD.augmentationPower 2)
    (hspan : (foxMap F P generators).ker =
      (⨆ j, globalFoxBlock P generators (localWords j)) ⊔ globalFoxBlock P generators words)
    (hrow : foxMap F P (fun j => FreeGroup.lift generators (words j))
      (fun i => induced F Dyadic.D f (c i)) = 0)
    (hcommon : globalDyadicRow P generators words f c ≤
      ⨆ j, globalFoxBlock P generators (localWords j))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ (1-(Fintype.card ι : ℝ)*t +
        (∑ j, ((Fintype.card (κ j) : ℝ)*t-1+
          1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (D j)))) +
        (3*t-1+1/((1+t)^3*(1+t^2)^2)) -
        t^2*(1-t^7/((1+t)^3*(1+t^2)^2)))*
        Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) := by
  have hi := finite_optimized_dyadic_block_inequality P hP generators hgen
    (fun j => globalFoxBlock P generators (localWords j)) words f hwords hfirst hsecond
    r hleft c hc hspan hrow hcommon t ht0 ht1
  have hcst := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    global_local_kernel_cost (D j) P (localMaps j) (hlayers j) (hlocalTwo j) hP
      (localGenerators j) generators (localWords j) (hlocalGen j) (hlocalWords j) t ht0 ht1)
  rw [← Finset.sum_mul] at hcst
  nlinarith

/-- The manuscript's rational optimized polynomial, independently defined
from the local group polynomials. Its exact negative test is a proved finite
rational computation, not a tower-existence hypothesis. -/
def optimizedTowerPolynomial (t : ℚ) : ℚ :=
  1-7*t + 2*(2*t-1+1/(1+t)^2) + 3*(2*t-1+1/((1+t)^2*(1+t^2))) +
    (3*t-1+1/((1+t)^3*(1+t^2)^2)) + t^2/(1+t) -
    t^2*(1-t^7/((1+t)^3*(1+t^2)^2)) + 5*t^4/((1+t)*(1+t^2))

theorem optimizedTowerPolynomial_test :
    optimizedTowerPolynomial (11/34) = -160218343/112275691650 := by
  norm_num [optimizedTowerPolynomial]

theorem optimizedTowerPolynomial_negative : optimizedTowerPolynomial (11/34) < 0 := by
  rw [optimizedTowerPolynomial_test]
  norm_num

end UnitDistance.GroupAugmentation
