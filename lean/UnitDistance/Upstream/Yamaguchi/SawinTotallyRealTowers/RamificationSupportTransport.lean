/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.RamificationSupport

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Ramification support under an equivalence of top fields

An algebra equivalence preserves the permitted finite places on the base.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v w

namespace ClassFieldTower.Sawin.IsUnramifiedAtFinitePlacesOutside

/-- Replacing the top number field by an equivalent algebra preserves
unramifiedness outside the same set of finite places of the base. -/
theorem congrTop
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) {S : Set (HeightOneSpectrum (𝓞 K))}
    (h : IsUnramifiedAtFinitePlacesOutside K L S) :
    IsUnramifiedAtFinitePlacesOutside K M S := by
  let : Algebra L M := e.toRingHom.toAlgebra
  let : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.commutes x).symm)
  let eLM : L ≃ₐ[L] M :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ ↦ rfl)
  let eOLM : (𝓞 L) ≃ₐ[𝓞 L] (𝓞 M) :=
    NumberField.RingOfIntegers.mapAlgEquiv eLM
  let : Algebra.FormallyUnramified (𝓞 L) (𝓞 M) :=
    Algebra.FormallyUnramified.of_equiv eOLM
  intro P hP
  let q : HeightOneSpectrum (𝓞 L) := finitePlaceBelow (K := L) P
  have hOutside : finitePlaceBelow (K := K) q ∉ S := by
    simpa only [q, finitePlaceBelow_finitePlaceBelow] using hP
  let : P.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  let : Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal := h q hOutside
  exact Algebra.IsUnramifiedAt.comp (R := 𝓞 K) q.asIdeal P.asIdeal

end ClassFieldTower.Sawin.IsUnramifiedAtFinitePlacesOutside
