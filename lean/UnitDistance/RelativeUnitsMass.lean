module

public import UnitDistance.RelativeUnitsRegulator
public import UnitDistance.RelativeClassNumber

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual relative-unit mass formula

All quantities are the independently defined arithmetic invariants: ordinary
class numbers, the kernel of actual ideal-class extension, actual torsion,
the covolume in actual unweighted relative coordinates, and the actual
relative Dedekind-zeta residue. Finite unramifiedness and the quadratic
signature are the only structural hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units
open UnitDistance.NumberFieldAnalysis

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The ordinary relative ideal-class quotient, used to count geometric fibers. -/
abbrev RelativeClassQuotient :=
  ClassGroup (𝓞 K) ⧸ (ClassGroup.extendedHom (𝓞 F) (𝓞 K)).range

/-- The number of actual relative ideal classes is exactly `h_rel κ`.
This finite-group identity needs no unramifiedness hypothesis. -/
theorem relativeClassQuotient_card_mul :
    Nat.card (RelativeClassQuotient (F := F) (K := K)) * classNumber F =
      classNumber K * Nat.card (CapitulationKernel (F := F) (K := K)) := by
  let f := ClassGroup.extendedHom (𝓞 F) (𝓞 K)
  have hk := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hk
  have hi := f.range.index_mul_card
  have h : f.range.index * Nat.card (ClassGroup (𝓞 F)) =
      Nat.card (ClassGroup (𝓞 K)) * Nat.card f.ker := by
    rw [← hk, ← hi]
    ring
  simpa only [Subgroup.index, Nat.card_eq_fintype_card, classNumber] using h

theorem relativeClassQuotient_card_real :
    (Nat.card (RelativeClassQuotient (F := F) (K := K)) : ℝ) =
      ((classNumber K : ℝ) / (classNumber F : ℝ)) *
        Nat.card (CapitulationKernel (F := F) (K := K)) := by
  have h := relativeClassQuotient_card_mul (F := F) (K := K)
  have hr : (Nat.card (RelativeClassQuotient (F := F) (K := K)) : ℝ) * classNumber F =
      (classNumber K : ℝ) * Nat.card (CapitulationKernel (F := F) (K := K)) := by
    exact_mod_cast h
  have hF : (classNumber F : ℝ) ≠ 0 := by exact_mod_cast (classNumber_pos F).ne'
  apply (eq_div_iff hF).mpr at hr
  rw [hr]
  ring

/-- The denominator of the geometric relative-unit mass, using actual class
extension and the ordinary unweighted relative-coordinate covolume. -/
def relativeMassDenominator (ι : K ≃ₐ[F] K) : ℝ :=
  ((classNumber K : ℝ) / (classNumber F : ℝ)) *
    Nat.card (CapitulationKernel (F := F) (K := K)) * relativeRegulator ι

theorem relativeMassDenominator_eq_classQuotient (ι : K ≃ₐ[F] K) :
    relativeMassDenominator ι =
      (Nat.card (RelativeClassQuotient (F := F) (K := K)) : ℝ) * relativeRegulator ι := by
  rw [relativeClassQuotient_card_real]
  rfl

theorem relativeMassDenominator_pos (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    0 < relativeMassDenominator ι := by
  unfold relativeMassDenominator
  exact mul_pos (mul_pos (div_pos (by exact_mod_cast classNumber_pos K)
    (by exact_mod_cast classNumber_pos F))
      (by exact_mod_cast Nat.card_pos (α := CapitulationKernel (F := F) (K := K))))
    (relativeRegulator_pos ι hι)

/-- The actual geometric mass `w_K / (h_rel κ R_U)`. -/
def relativeUnitMass (ι : K ≃ₐ[F] K) : ℝ :=
  (torsionOrder K : ℝ) / relativeMassDenominator ι

theorem relativeUnitMass_pos (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    0 < relativeUnitMass ι :=
  div_pos (by exact_mod_cast torsionOrder_pos K) (relativeMassDenominator_pos ι hι)

/-- The actual relative mass identity, in ordinary discriminant normalization. -/
theorem relativeUnitMass_eq (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    relativeUnitMass ι =
      (2 : ℝ) ^ (Module.finrank ℚ F - 1) * Real.pi ^ (nrRealPlaces F + nrComplexPlaces F) /
        (Real.sqrt (absoluteDiscriminant F) * relativeResidue K F) := by
  obtain ⟨ρ, σ, hbase, hconj⟩ := exists_complexifying_embeddings ι hι hb
  have hc := relativeClassRegulator_eq K F
    (Algebra.IsQuadraticExtension.finrank_eq_two F K) hunr ρ
  have hi : (normUnitImage (F := F) (K := K)).index =
      Nat.card (CapitulationKernel (F := F) (K := K)) * 2 ^ (nrRealPlaces F - 1) := by
    rw [unitNorm_index_eq_unitH1_mul_pow_real_places ι hι hb,
      capitulation_card_eq_unitH1_card hunr ι hι]
  have hF : (classNumber F : ℝ) ≠ 0 := by exact_mod_cast (classNumber_pos F).ne'
  have hr : relativeClassRegulator K F = relativeMassDenominator ι *
      ((2 : ℝ) ^ nrComplexPlaces F / 2 * (2 : ℝ) ^ (nrRealPlaces F - 1)) := by
    unfold relativeClassRegulator relativeMassDenominator
    rw [regulator_eq_relativeRegulator_mul_normIndex ι hι hb, hi,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp [regulator_ne_zero F, hF]
  have hp : (2 : ℝ) ^ (Module.finrank ℚ F - 1) =
      (2 : ℝ) ^ (nrRealPlaces F - 1) *
        (2 : ℝ) ^ nrComplexPlaces F * (2 : ℝ) ^ nrComplexPlaces F := by
    rw [← pow_add, ← pow_add]
    congr 1
    have hd := card_add_two_mul_card_eq_rank F
    omega
  rw [hr] at hc
  have hpi : Real.pi ^ (nrRealPlaces F + nrComplexPlaces F) ≠ 0 :=
    pow_ne_zero _ Real.pi_ne_zero
  have htwo : (2 : ℝ) ^ nrComplexPlaces F ≠ 0 := by positivity
  have hden := (relativeMassDenominator_pos ι hι).ne'
  have hres := (relativeResidue_pos K F).ne'
  have hD := (Real.sqrt_pos.mpr (absoluteDiscriminant_pos F)).ne'
  rw [pow_succ] at hc
  field_simp [htwo, hpi] at hc
  unfold relativeUnitMass
  rw [hp]
  field_simp [hden, hres, hD]
  nlinarith [hc]

/-- The manuscript's exact root-discriminant normalization of the mass. -/
theorem relativeUnitMass_eq_rootDiscriminant (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    relativeUnitMass ι =
      (2 : ℝ) ^ (Module.finrank ℚ F - 1) * Real.pi ^ (nrRealPlaces F + nrComplexPlaces F) /
        (rootDiscriminant F ^ ((Module.finrank ℚ F : ℝ) / 2) * relativeResidue K F) := by
  rw [relativeUnitMass_eq hunr ι hι hb,
    sqrt_absoluteDiscriminant_eq_rootDiscriminant_rpow F]

/-- The mass formula with the literal cardinality of the actual relative
ideal-class quotient, ready for the arithmetic fiber-counting construction. -/
theorem classQuotient_mass_formula (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    (torsionOrder K : ℝ) /
        ((Nat.card (ClassGroup (𝓞 K) ⧸ (ClassGroup.extendedHom (𝓞 F) (𝓞 K)).range) : ℝ) *
          relativeRegulator ι) =
      (2 : ℝ) ^ (Module.finrank ℚ F - 1) * Real.pi ^ (nrRealPlaces F + nrComplexPlaces F) /
        (rootDiscriminant F ^ ((Module.finrank ℚ F : ℝ) / 2) * relativeResidue K F) := by
  rw [← relativeMassDenominator_eq_classQuotient ι]
  exact relativeUnitMass_eq_rootDiscriminant hunr ι hι hb

end UnitDistance.RelativeUnits
