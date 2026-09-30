module

public import UnitDistance.FieldTensorCyclicH2
public import UnitDistance.OneInfinitePlaceNorm
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm

@[expose] public section
set_option backward.privateInPublic true


/-! Finite-place detection of cyclic field-unit H² over a base with one
infinite place. The proof uses the actual tensor norm and global reciprocity maps. -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped TensorProduct NumberField
namespace UnitDistance.ArithmeticProP
open GlobalClassFieldTheory.ClassFieldAxiom

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
variable [IsAbelianGalois K L] [IsCyclic Gal(L/K)]
variable [Subsingleton (InfinitePlace K)]

/-- All actual finite tensor localizations jointly detect cyclic field-unit
H²; global reciprocity eliminates the single infinite coordinate. -/
theorem finiteCyclicFieldUnitsH2_eq_zero_of_finiteTensor_eq_zero
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K),
      (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) : x = 0 := by
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨b,rfl⟩ := exists_fieldScalarUnitH2 K L g hg x
  apply (fieldScalarUnitH2_eq_zero_iff_norm K L g hg b).mpr
  apply global_norm_of_finite_local_norms K L b
  intro v
  have hb := (fieldScalarUnitH2_tensor_eq_zero_iff_norm K L
    (v.adicCompletion K) g hg b).mp (hx v)
  rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
  exact hb

end UnitDistance.ArithmeticProP
