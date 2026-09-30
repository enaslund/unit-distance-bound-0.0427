module

public import UnitDistance.GroupAugmentationInducedHilbert
public import UnitDistance.JenningsFilteredInduction
public import UnitDistance.JenningsDyadicHilbert

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual normalized full local Fox-kernel costs

The proved subgroup-compatible Jennings coordinates specialize the full
induced-kernel Hilbert identity. For the actual dyadic group, first-two-layer
injection alone gives the exact cost `(3t-1+1/P_D(t))*H_A(t)` appearing in the
optimized infinitude argument.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open FilteredHilbert
local notation "F" => ZMod 2
section General
variable (D P : Type*) [Group D] [Group P] [Finite D] [Finite P]
variable (f : D →* P) (hinj : ∀ n, Function.Injective (layerMap F D f n))
variable (hD : IsPGroup 2 D) (hP : IsPGroup 2 P)
variable {ι : Type*} [Fintype ι]
variable (generators : ι → D) (hgen : Subgroup.closure (Set.range generators) = ⊤)

theorem shiftPolynomial_eval (x : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) x (shiftPolynomial D P f hinj hP) =
      ∑ t : ComplementChoices D P f hinj, x^(complementWeight D P f hinj hP t) := by
  simp [shiftPolynomial,Polynomial.eval₂_finsetSum,Polynomial.eval₂_monomial]

include hD hgen in
/-- The full actual induced local augmentation kernel has the exact
normalized cost supplied by the actual complementary shift polynomial. -/
theorem jennings_induced_kernel_value (x : ℝ) :
    value F (ι → A F P) (foxKernelPower P (fun i => f (generators i))) (Nat.card P+1) x =
      ((Fintype.card ι : ℝ)*x-1)*
        Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial P) +
          Polynomial.eval₂ (Nat.castRingHom ℝ) x (shiftPolynomial D P f hinj hP) := by
  have he := value_induced_foxKernel_standard D hD P (ComplementChoices D P f hinj) f
    (filteredCoordinates D P f hinj hD hP) (complementWeight D P f hinj hP)
    (filteredCoordinates_mul D P f hinj hD hP)
    (filteredCoordinates_mem_power_iff D P f hinj hD hP) generators hgen hP x
  rw [← shiftPolynomial_eval D P f hinj hP] at he
  have hf := congrArg (Polynomial.eval₂ (Nat.castRingHom ℝ) x)
    (hilbertPolynomial_induction D P f hinj hD hP)
  rw [Polynomial.eval₂_mul] at hf
  rw [he]
  nlinarith [hf]

end General
open Dyadic
variable (P : Type*) [Group P] [Finite P] (hP : IsPGroup 2 P)
variable (f : Dyadic.D →* P)
variable (hfirst : Function.Injective (layerMap F Dyadic.D f 1))
variable (hsecond : Function.Injective (layerMap F Dyadic.D f 2))

include hP hfirst hsecond in
/-- The actual full dyadic kernel, with its induced ambient filtration,
has precisely the optimized dyadic cost. Only actual ambient first-two-layer
injections remain as group-specific hypotheses. -/
theorem dyadic_induced_kernel_cost (x : ℝ) (hx : 0 ≤ x) :
    value F (Fin 3 → A F P) (foxKernelPower P (fun i => f (Filtration.gen i))) (Nat.card P+1) x =
      (3*x-1+1/((1+x)^3*(1+x^2)^2))*
        Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial P) := by
  rw [jennings_induced_kernel_value Dyadic.D P f
    (dyadic_layer_injections P f hfirst hsecond) dyadic_isTwoGroup hP
    Filtration.gen dyadic_generators]
  rw [dyadic_shiftPolynomial_eval P hP f hfirst hsecond x hx]
  norm_num only [Fintype.card_fin,Nat.cast_ofNat]
  ring

end UnitDistance.GroupAugmentation
