module

public import UnitDistance.RelativeUnitsLogLattice
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

@[expose] public section
set_option backward.privateInPublic true


/-!
# Complexifying embeddings are derived from the actual quadratic signature

The compatibility data used in relative-unit positivity are constructed here
from the ordinary field hypotheses. They are not additional structural inputs.
-/

noncomputable section
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- A totally complex quadratic extension above a base with a real place has
actual compatible embeddings under which its nontrivial automorphism is complex
conjugation. Existence follows from the Galois action on infinite places. -/
theorem exists_complexifying_embeddings (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) :
    ∃ (ρ : F →+* ℝ) (σ : K →+* ℂ),
      (∀ x : F, σ (algebraMap F K x) = (ρ x : ℂ)) ∧
      (∀ x : K, σ (ι x) = star (σ x)) := by
  obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp hb
  obtain ⟨v, hv⟩ := comap_surjective (K := K) w
  have hvram : v.IsRamified F := isRamified_iff.mpr
    ⟨IsTotallyComplex.isComplex v, by simpa only [hv] using hw⟩
  obtain ⟨g, hg⟩ := exists_isConj_of_isRamified
    (show IsRamified F (mk v.embedding) by rw [mk_embedding]; exact hvram)
  have hgne : g ≠ 1 := (ComplexEmbedding.isConj_ne_one_iff hg).mpr
    (isComplex_iff.mp (IsTotallyComplex.isComplex v))
  have hgι : g = ι := (automorphism_eq_one_or ι hι g).resolve_left hgne
  rw [hgι] at hg
  refine ⟨hg.isReal_comp.embedding, v.embedding, ?_, hg.eq⟩
  intro x
  exact (ComplexEmbedding.IsReal.coe_embedding_apply hg.isReal_comp x).symm

/-- No independently supplied embedding compatibility is needed for the
root-of-unity norm-one fact in the paper's field signature. -/
theorem torsion_le_normOneUnits_of_totallyComplex
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    torsion K ≤ normOneUnits (F := F) (K := K) := by
  obtain ⟨ρ, σ, hbase, hconj⟩ := exists_complexifying_embeddings ι hι hb
  exact torsion_le_normOneUnits ι hι ρ σ hbase hconj

/-- The logarithmic norm sequence is exact from actual signature hypotheses alone. -/
theorem normLogLattice_ker_eq_of_totallyComplex
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    (normLogLattice (F := F) (K := K)).ker = relativeLogLattice (F := F) (K := K) := by
  obtain ⟨ρ, σ, hbase, hconj⟩ := exists_complexifying_embeddings ι hι hb
  exact normLogLattice_ker_eq ι hι ρ σ hbase hconj

/-- The norm-image covolume formula follows from actual quadratic field and
signature data, without a norm-sign or embedding-compatibility hypothesis. -/
theorem normImageLogLattice_covolume_of_totallyComplex
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    ZLattice.covolume (normImageLogLattice (F := F) (K := K)) =
      ((normUnitImage (F := F) (K := K)).index : ℝ) / 2 * regulator F := by
  obtain ⟨ρ, σ, hbase, hconj⟩ := exists_complexifying_embeddings ι hι hb
  exact normImageLogLattice_covolume ι hι ρ σ hbase hconj

end UnitDistance.RelativeUnits
