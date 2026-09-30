/-
B-analogue of `UnitDistance/RationalFiniteFieldUnitsH2Reduction.lean` and
`UnitDistance/RationalFiniteFieldUnitsH2.lean`: over `B` the finite places
detect field-unit H² of a finite Galois 2-extension only up to a kernel of at
most two elements, coming from the two real places. The image version of the
tower lemma generalizes `UnitDistance/FiniteTensorTowerDetection.lean`.
-/
module

public import UnitDistance.Sqrt241.Relation.QuadraticDetection
public import UnitDistance.Sqrt241.Relation.ImaginaryB
public import UnitDistance.Sqrt241.Relation.KummerCount
public import UnitDistance.FiniteTensorTowerDetection
public import UnitDistance.TotallyComplexFieldUnitsH2

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Finite-place detection of field-unit H² over `B` up to two classes

For a finite Galois 2-extension `L/B`, inflate to `N = L(i)`; restriction to
`Gal(N/B(i))` is detected at finite places because `B(i)` is totally complex;
the tower exactness puts the class in the inflation image of the detection
kernel of `B(i)/B`, which has at most two elements (two real places of `B`).
Inflation from `L` to `N` is injective, so the detection kernel of `L/B` has at
most two elements: `finiteDetectionPair_B : FiniteDetectionPair B`.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Cohomology UnitDistance.ArithmeticProP

section Tower

variable (K F L : Type) [Field K] [NumberField K] [Field F] [NumberField F]
variable [Field L] [NumberField L]
variable [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
variable [FiniteDimensional K F] [FiniteDimensional K L]
variable [IsGalois K F] [IsGalois K L]

/-- Image version of `fieldUnitsH2_finite_detection_tower`: a class of the top
extension vanishing at every finite place is inflated from a class of the
bottom extension lying in any prescribed set containing the bottom detection
kernel. -/
theorem fieldUnitsH2_finite_detection_tower_mem_image
    (hrelative : ∀ y : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2,
      (∀ w : HeightOneSpectrum (𝓞 F),
        (fieldUnitsTensorH2 F L (w.adicCompletion F)).hom y = 0) → y = 0)
    (D : Set (groupCohomology (Rep.ofAlgebraAutOnUnits K F) 2))
    (hlower : ∀ y : groupCohomology (Rep.ofAlgebraAutOnUnits K F) 2,
      (∀ v : HeightOneSpectrum (𝓞 K),
        (fieldUnitsTensorH2 K F (v.adicCompletion K)).hom y = 0) → y ∈ D)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K),
      (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) :
    x ∈ (finiteGaloisTowerUnitsH2Inflation K F L).hom '' D := by
  have hres : (finiteGaloisTowerUnitsH2Restriction K F L).hom x = 0 := by
    apply hrelative
    intro w
    exact finiteFieldUnitsTensorRestriction_eq_zero_of_eq_zero K F L
      (finitePlaceBelow (K := K) w) ⟨w, rfl⟩ x (hx _)
  obtain ⟨y, hy⟩ := finiteGaloisTowerUnitsH2Restriction_ker_le_inflation_range
    K F L hres
  refine ⟨y, hlower y ?_, hy⟩
  intro v
  apply (finiteFieldUnitsTensor_inflation_eq_zero_iff K F L v y).mp
  rw [hy]
  exact hx v

end Tower

open Base

/-- The finite-place detection kernel of `B(i)/B` has at most two elements. -/
theorem imaginaryB_pair :
    ∃ z₀ : groupCohomology (Rep.ofAlgebraAutOnUnits B ImaginaryB.Carrier) 2, ∀ z,
      (∀ v : HeightOneSpectrum (𝓞 B),
        (fieldUnitsTensorH2 B ImaginaryB.Carrier (v.adicCompletion B)).hom z = 0) →
        z = 0 ∨ z = z₀ :=
  finiteQuadraticFieldUnitsH2_pair B ImaginaryB.Carrier ImaginaryB.natCard_gal
    placePlus placeMinus infinitePlace_eq

set_option maxHeartbeats 400000 in
/-- Over `B`, the finite-place detection kernel of field-unit H² of every
finite Galois 2-extension has at most two elements. -/
theorem finiteDetectionPair_B : FiniteDetectionPair B := by
  intro L _ _ _ _ _ hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := imaginaryGaloisEnlargement L
  have : IsGalois B N := N.isGalois
  let e : L →ₐ[B] N := imaginaryGaloisEnlargementEmbedding L
  let : Algebra L N := e.toRingHom.toAlgebra
  have : IsScalarTower B L N := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (e.commutes a).symm)
  obtain ⟨i, hi⟩ := imaginaryGaloisEnlargement_has_root L
  let eF : ImaginaryB.Carrier →ₐ[B] N := ImaginaryB.embedding i hi
  let : Algebra ImaginaryB.Carrier N := eF.toRingHom.toAlgebra
  have : IsScalarTower B ImaginaryB.Carrier N := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (eF.commutes a).symm)
  have : IsGalois ImaginaryB.Carrier N := IsGalois.tower_top_of_isGalois B ImaginaryB.Carrier N
  have hPN : IsPGroup 2 Gal(N/B) := imaginaryGaloisEnlargement_isPGroup L hP
  have hPF : IsPGroup 2 Gal(N/ImaginaryB.Carrier) := hPN.of_injective
    (AlgEquiv.restrictScalarsHom B) (AlgEquiv.restrictScalars_injective B)
  obtain ⟨z₀, hz₀⟩ := imaginaryB_pair
  have hmem : ∀ x : groupCohomology (Rep.ofAlgebraAutOnUnits B L) 2,
      (∀ v : HeightOneSpectrum (𝓞 B),
        (fieldUnitsTensorH2 B L (v.adicCompletion B)).hom x = 0) →
      (finiteGaloisTowerUnitsH2Inflation B L N).hom x = 0 ∨
        (finiteGaloisTowerUnitsH2Inflation B L N).hom x =
          (finiteGaloisTowerUnitsH2Inflation B ImaginaryB.Carrier N).hom z₀ := by
    intro x hx
    have hN : ∀ v : HeightOneSpectrum (𝓞 B),
        (fieldUnitsTensorH2 B N (v.adicCompletion B)).hom
          ((finiteGaloisTowerUnitsH2Inflation B L N).hom x) = 0 :=
      fun v => (finiteFieldUnitsTensor_inflation_eq_zero_iff B L N v x).mpr (hx v)
    obtain ⟨y, hy, hyx⟩ := fieldUnitsH2_finite_detection_tower_mem_image
      B ImaginaryB.Carrier N
      (fieldUnitsH2_eq_zero_of_finite_localizations ImaginaryB.Carrier N (p := 2) hPF)
      {0, z₀} (fun y hy => hz₀ y hy) _ hN
    rcases hy with rfl | rfl
    · left
      rw [← hyx, map_zero]
    · right
      exact hyx.symm
  have hinj := finiteGaloisTowerUnitsH2Inflation_injective B L N
  by_cases hex : ∃ x₁ : groupCohomology (Rep.ofAlgebraAutOnUnits B L) 2,
      (∀ v : HeightOneSpectrum (𝓞 B),
        (fieldUnitsTensorH2 B L (v.adicCompletion B)).hom x₁ = 0) ∧ x₁ ≠ 0
  · obtain ⟨x₁, hx₁, hne⟩ := hex
    refine ⟨x₁, fun x hx => ?_⟩
    rcases hmem x hx with h | h
    · left
      apply hinj
      rw [h, map_zero]
    · right
      rcases hmem x₁ hx₁ with h₁ | h₁
      · exact absurd (hinj (h₁.trans (map_zero _).symm)) hne
      · exact hinj (h.trans h₁.symm)
  · push Not at hex
    exact ⟨0, fun x hx => Or.inl (hex x hx)⟩

end UnitDistance.Sqrt241.Relation
