module

public import UnitDistance.RelativeUnitsHilbert90

@[expose] public section
set_option backward.privateInPublic true


/-!
# The cyclic norm-one/coboundary quotient of actual quadratic units

This module constructs the ordinary cyclic degree-one cohomology presentation
`ker(1+ι) / image(1-ι)` on actual integral units. Its relation to the
capitulation kernel requires unramified descent of invariant ideals separately.
-/

noncomputable section
open scoped NumberField

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- The ordinary unit coboundary, valued in actual relative norm-one units. -/
def unitCoboundary (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    (𝓞 K)ˣ →* normOneUnits (F := F) (K := K) where
  toFun u := ⟨u / unitInvolution ι u, by
    rw [mem_normOneUnits_iff ι hι, map_div, unitInvolution_involutive ι hι]
    simp [div_eq_mul_inv, mul_assoc]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' u v := by
    apply Subtype.ext
    change u * v / unitInvolution ι (u * v) = (u / unitInvolution ι u) * (v / unitInvolution ι v)
    rw [map_mul, mul_div_mul_comm]

/-- A unit has trivial coboundary precisely when the actual involution fixes it. -/
theorem unitCoboundary_eq_one_iff (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (u : (𝓞 K)ˣ) :
    unitCoboundary ι hι u = 1 ↔ unitInvolution ι u = u := by
  rw [← Subtype.val_inj]
  change u / unitInvolution ι u = 1 ↔ _
  rw [div_eq_one, eq_comm]

/-- The cyclic norm-one/coboundary quotient, independently defined from unit arithmetic. -/
abbrev UnitH1 (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :=
  normOneUnits (F := F) (K := K) ⧸ (unitCoboundary ι hι).range

/-- The involution on norm-one units is inversion. -/
theorem unitInvolution_eq_inv (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : normOneUnits (F := F) (K := K)) : unitInvolution ι u.val = u.val⁻¹ := by
  have h := (mem_normOneUnits_iff ι hι u.val).mp u.property
  exact (eq_inv_iff_mul_eq_one).mpr (by simpa [mul_comm] using h)

/-- Every norm-one square is an actual unit coboundary. -/
theorem normOne_square_mem_coboundary (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : normOneUnits (F := F) (K := K)) : u ^ 2 ∈ (unitCoboundary ι hι).range := by
  refine ⟨u.val, ?_⟩
  apply Subtype.ext
  change u.val / unitInvolution ι u.val = u.val ^ 2
  rw [unitInvolution_eq_inv ι hι, div_inv_eq_mul, pow_two]

/-- Degree-one cyclic unit cohomology is killed by two. -/
theorem unitH1_sq (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : UnitH1 ι hι) : x ^ 2 = 1 := by
  change x ^ 2 = (1 : normOneUnits (F := F) (K := K) ⧸ (unitCoboundary ι hι).range)
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact normOne_square_mem_coboundary ι hι u

/-- Relative units are finitely generated, by Dirichlet and Noetherianity over `ℤ`. -/
instance normOneUnits_groupFG : Group.FG (normOneUnits (F := F) (K := K)) := by
  apply (Group.fg_iff_subgroup_fg _).mpr
  rw [Subgroup.fg_iff_add_fg]
  exact (Submodule.fg_iff_addSubgroup_fg _).mp
    (IsNoetherian.noetherian (normOneUnits (F := F) (K := K)).toAddSubgroup.toIntSubmodule)

/-- The actual cyclic unit-cohomology quotient is finite. Its size is not assumed. -/
instance unitH1_finite (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) : Finite (UnitH1 ι hι) := by
  apply CommGroup.finite_of_fg_torsion
  intro x
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, unitH1_sq ι hι x⟩

/-- The kernel of the unit coboundary consists exactly of embedded base units. -/
theorem unitCoboundary_ker (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    (unitCoboundary ι hι).ker = (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom).range := by
  ext u
  rw [MonoidHom.mem_ker, unitCoboundary_eq_one_iff, unitInvolution_fixed_iff ι hι]
  rfl

end UnitDistance.RelativeUnits
