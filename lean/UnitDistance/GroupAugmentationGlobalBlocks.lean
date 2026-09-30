module

public import UnitDistance.GroupAugmentationFoxSubstitution
public import UnitDistance.GroupAugmentationCoefficientInjection
public import UnitDistance.FilteredHilbertMaps
public import UnitDistance.JenningsDyadicRowHilbert

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual global relation blocks and their optimized Hilbert costs

Local kernels are mapped by the actual Fox matrix of chosen global words.
Their induced Hilbert values are bounded by the local kernel values. An
actual elementary left inverse makes the common-row map strict and injective,
so its certified dyadic cost is preserved exactly in global coordinates.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open FilteredHilbert
variable (P : Type*) [Group P] [Finite P]
local notation "F" => ZMod 2
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (generators : ι → P) (words : κ → FreeGroup ι)

/-- The actual image of a local augmentation kernel in global Fox coordinates. -/
def globalFoxBlock : Submodule F (ι → A F P) :=
  ((foxMap F P (fun j => FreeGroup.lift generators (words j))).ker).map
    (foxSubstitution F P generators words)

theorem globalFoxBlock_le_kernel :
    globalFoxBlock P generators words ≤ (foxMap F P generators).ker :=
  foxSubstitution_kernel_le F P generators words

/-- The global block map charges at most the full actual local kernel value;
no quotient-module injection is needed for this upper bound. -/
theorem globalFoxBlock_value_le (hP : IsPGroup 2 P)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value F (ι → A F P)
      (fun n => globalFoxBlock P generators words ⊓ shiftedFoxCoefficientPower P n)
      (Nat.card P+1) t ≤
    value F (κ → A F P)
      (foxKernelPower P (fun j => FreeGroup.lift generators (words j)))
      (Nat.card P+1) t := by
  have he := value_induced_map_le F (κ → A F P) (ι → A F P)
    (shiftedFoxCoefficientPower P) (shiftedFoxCoefficientPower P)
    (shiftedFoxCoefficientPower_antitone P) (shiftedFoxCoefficientPower_zero P)
    (shiftedFoxCoefficientPower_zero P) (foxSubstitution F P generators words)
    (fun n => foxSubstitution_filtered F P generators words (n-1))
    (foxMap F P (fun j => FreeGroup.lift generators (words j))).ker (Nat.card P+1)
    (shiftedFoxCoefficientPower_nilpotent P hP _ le_rfl)
    (shiftedFoxCoefficientPower_nilpotent P hP _ le_rfl) t ht0 ht1
  have hk : (fun n => (foxMap F P (fun j => FreeGroup.lift generators (words j))).ker ⊓
      shiftedFoxCoefficientPower P n) =
      foxKernelPower P (fun j => FreeGroup.lift generators (words j)) := by
    funext n
    exact inf_comm _ _
  rw [hk] at he
  exact he

variable (hP : IsPGroup 2 P)

include hP in
/-- The full actual dyadic block has the optimized upper cost in the global
Fox module, using the genuine layer injections and actual word evaluation. -/
theorem global_dyadic_block_cost (words : Fin 3 → FreeGroup ι)
    (f : Dyadic.D →* P)
    (hwords : ∀ j, FreeGroup.lift generators (words j) = f (Dyadic.Filtration.gen j))
    (hfirst : Function.Injective (layerMap F Dyadic.D f 1))
    (hsecond : Function.Injective (layerMap F Dyadic.D f 2))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value F (ι → A F P)
      (fun n => globalFoxBlock P generators words ⊓ shiftedFoxCoefficientPower P n)
      (Nat.card P+1) t ≤
    (3*t-1+1/((1+t)^3*(1+t^2)^2))*
      Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) := by
  have he := globalFoxBlock_value_le P generators words hP t ht0 ht1
  simp_rw [hwords] at he
  rw [dyadic_induced_kernel_cost P hP f hfirst hsecond t ht0] at he
  exact he

/-- The actual image of the induced dyadic common row in global coordinates. -/
def globalDyadicRow (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
    (c : Fin 3 → Dyadic.AlgebraD) : Submodule F (ι → A F P) :=
  ((coefficientRow F P (fun i => induced F Dyadic.D f (c i))).range).map
    (foxSubstitution F P generators words)

include hP in
/-- The proved actual dyadic row cost survives the global coordinate change
as soon as its matrix has an actual elementary left inverse. -/
theorem global_dyadic_row_cost (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
    (hfirst : Function.Injective (layerMap F Dyadic.D f 1))
    (hsecond : Function.Injective (layerMap F Dyadic.D f 2))
    (r : (ι → A F P) →ₗ[A F P] (Fin 3 → A F P))
    (hleft : ∀ j k, augmentation F P
        (r (foxSubstitutionAlgebra F P generators words (Pi.single j 1)) k) =
      augmentation F P ((Pi.single j (1 : A F P) : Fin 3 → A F P) k))
    (c : Fin 3 → Dyadic.AlgebraD)
    (hc : ∀ i, c i-Dyadic.AlgebraD.linearFoxCoefficients i ∈ Dyadic.AlgebraD.augmentationPower 2)
    (t : ℝ) (ht0 : 0 ≤ t) :
    value F (ι → A F P)
      (fun n => globalDyadicRow P generators words f c ⊓ shiftedFoxCoefficientPower P n)
      (Nat.card P+1) t =
    t^2*(1-t^7/((1+t)^3*(1+t^2)^2))*
      Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) := by
  rw [globalDyadicRow,foxSubstitution,
    coefficientLinearMap_value_eq P hP (foxSubstitutionAlgebra F P generators words) r hleft]
  exact dyadic_induced_row_cost P hP f hfirst hsecond c hc t ht0

/-- The row range of an actual local relation lies in the full global block.
This is actual vector inclusion, independent of its Hilbert cost. -/
theorem globalDyadicRow_le_block (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
    (c : Fin 3 → Dyadic.AlgebraD)
    (hrow : foxMap F P (fun j => FreeGroup.lift generators (words j))
      (fun i => induced F Dyadic.D f (c i)) = 0) :
    globalDyadicRow P generators words f c ≤ globalFoxBlock P generators words := by
  apply Submodule.map_mono
  rintro a ⟨b,rfl⟩
  change foxMap F P (fun j => FreeGroup.lift generators (words j))
    (b • (fun i => induced F Dyadic.D f (c i))) = 0
  change foxMapAlgebra F P (fun j => FreeGroup.lift generators (words j))
    (b • (fun i => induced F Dyadic.D f (c i))) = 0
  rw [map_smul]
  change b • foxMap F P (fun j => FreeGroup.lift generators (words j))
    (fun i => induced F Dyadic.D f (c i)) = 0
  rw [hrow,smul_zero]

end UnitDistance.GroupAugmentation
