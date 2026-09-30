/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ExtensionBehavior
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleValue
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Norm-one correction for the normalized cyclotomic idele value

The positive archimedean section over `ℚ` gives the source term in the
cyclotomic norm-one reduction.  After taking a positive
`[K : ℚ]`-th root of the absolute norm of an idele, scalar extension of
that section cancels the absolute norm.  Its rational cyclotomic Artin
value is trivial, so the normalized value is unchanged.
-/

open scoped NNReal NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type) [Field K] [NumberField K]

/-- Every idele has the same normalized cyclotomic value as an actual
norm-one idele. -/
theorem
    exists_normOneIdele_same_normalizedCyclotomicZHatIdeleValue
    (a : IdeleGroup K) :
    ∃ b : IdeleGroup.normOneSubgroup (K := K),
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul (b : IdeleGroup K)) =
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a) := by
  let d := Module.finrank ℚ K
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  let r : ℝ≥0ˣ := IdeleGroup.absoluteNorm a
  have hrpos : 0 < (r : ℝ≥0) :=
    pos_iff_ne_zero.mpr r.ne_zero
  let s0 : ℝ≥0 := (r : ℝ≥0) ^ ((d : ℝ)⁻¹)
  have hs0pos : 0 < s0 := by
    exact NNReal.rpow_pos hrpos
  let s : ℝ≥0ˣ := Units.mk0 s0 hs0pos.ne'
  have hs_pow : s ^ d = r := by
    apply Units.ext
    change s0 ^ d = (r : ℝ≥0)
    exact NNReal.rpow_inv_natCast_pow (r : ℝ≥0) hd
  let c : IdeleGroup K :=
    relativeIdeleBaseChangeMulEquiv
      (K := ℚ) (L := K)
      (RelativeIdeleGroup.inclusion ℚ K
        (rationalPositiveArchimedeanIdele s))
  have hc_absoluteNorm :
      IdeleGroup.absoluteNorm c = r⁻¹ := by
    change
      IdeleGroup.absoluteNorm
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K)
            (RelativeIdeleGroup.inclusion ℚ K
              (rationalPositiveArchimedeanIdele s))) =
        r⁻¹
    change
      IdeleGroup.absoluteNorm
          (IdeleGroup.extension ℚ K
            (rationalPositiveArchimedeanIdele s)) = r⁻¹
    have hfinite :
        (IdeleGroup.extension ℚ K
          (rationalPositiveArchimedeanIdele s)).2 = 1 := by
      apply RestrictedProduct.ext
      intro w
      change IdeleGroup.finiteComponent w
          (IdeleGroup.extension ℚ K
            (rationalPositiveArchimedeanIdele s)) = 1
      rw [IdeleGroup.extension_finiteComponent,
        rationalPositiveArchimedeanIdele_finiteComponent, map_one]
    have hsource :
        nnnormUnitHom Rat.infinitePlace.Completion
            (IdeleGroup.infiniteComponent Rat.infinitePlace
              (rationalPositiveArchimedeanIdele s)) = s := by
      have hcomponent := congrArg Units.val
        (rationalPositiveArchimedeanIdele_infiniteComponent s)
      have hcomponent' :
          InfinitePlace.Completion.ringEquivRealOfIsReal
              Rat.isReal_infinitePlace
              ((IdeleGroup.infiniteComponent Rat.infinitePlace
                (rationalPositiveArchimedeanIdele s) :
                  Rat.infinitePlace.Completionˣ) :
                Rat.infinitePlace.Completion) =
            ((s : ℝ≥0ˣ) : ℝ) := by
        simpa using hcomponent
      apply Units.ext
      apply NNReal.eq
      rw [nnnormUnitHom_val]
      simp only [coe_nnnorm]
      calc
        ‖((IdeleGroup.infiniteComponent Rat.infinitePlace
            (rationalPositiveArchimedeanIdele s) :
              Rat.infinitePlace.Completionˣ) :
            Rat.infinitePlace.Completion)‖ =
            ‖InfinitePlace.Completion.ringEquivRealOfIsReal
              Rat.isReal_infinitePlace
              ((IdeleGroup.infiniteComponent Rat.infinitePlace
                (rationalPositiveArchimedeanIdele s) :
                  Rat.infinitePlace.Completionˣ) :
                Rat.infinitePlace.Completion)‖ :=
          ((InfinitePlace.Completion.isometryEquivRealOfIsReal
            Rat.isReal_infinitePlace).isometry.norm_map_of_map_zero
            (map_zero
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                Rat.isReal_infinitePlace)) _).symm
        _ = ‖((s : ℝ≥0ˣ) : ℝ)‖ := by rw [hcomponent']
        _ = (s : ℝ≥0) :=
          Real.norm_of_nonneg (s : ℝ≥0).coe_nonneg
    have hExtComponent (W : InfinitePlace K) :
        IdeleGroup.infiniteComponent W
            (IdeleGroup.extension ℚ K
              (rationalPositiveArchimedeanIdele s)) =
          let v := _root_.infinitePlaceBelow (K := ℚ) W
          letI : W.1.LiesOver v.1 := ⟨rfl⟩
          Units.map
            (NumberField.LiesOver.completionMap (v := v) (w := W))
            (IdeleGroup.infiniteComponent v
              (rationalPositiveArchimedeanIdele s)) := by
      let v := _root_.infinitePlaceBelow (K := ℚ) W
      letI : W.1.LiesOver v.1 := ⟨rfl⟩
      letI : Algebra ℚ ℚ := Algebra.id ℚ
      letI : Algebra ℚ (WithAbs v.1) :=
        WithAbs.instAlgebra _
      letI : UniformContinuousConstSMul ℚ
          (WithAbs v.1) :=
        WithAbs.instUniformContinuousConstSMulReal _
      letI : Algebra ℚ v.Completion := inferInstance
      apply Units.ext
      change
        (ContinuousMulEquiv.piUnits
          (IdeleGroup.extension ℚ K
            (rationalPositiveArchimedeanIdele s)).1 W : W.Completion) = _
      change
        (ContinuousMulEquiv.piUnits
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K)
            (RelativeIdeleGroup.inclusion ℚ K
              (rationalPositiveArchimedeanIdele s))).1 W :
          W.Completion) = _
      rw [_root_.relativeIdeleBaseChangeMulEquiv_infinite]
      let f := _root_.relativeInfiniteTensorPiMulEquiv
        (K := ℚ) (L := K)
        ((_root_.relativeIdeleToLocalData
          (K := ℚ) (L := K)
          (RelativeIdeleGroup.inclusion ℚ K
            (rationalPositiveArchimedeanIdele s))).infinite)
      change
        (ContinuousMulEquiv.piUnits
          (ContinuousMulEquiv.piUnits.symm f) W : W.Completion) = _
      rw [ContinuousMulEquiv.piUnits.apply_symm_apply]
      dsimp only [f]
      rw [_root_.relativeInfiniteTensorPiMulEquiv_apply]
      simp only [_root_.relativeIdeleToLocalData]
      rw [RelativeIdeleGroup.infiniteComponent_inclusion]
      rw [_root_.infinitePlaceTensorUnitsEquivAbove_apply]
      simp only [Units.coe_map]
      change
        _root_.infinitePlaceTensorRingEquivAbove
            (K := ℚ) (L := K) v
            ((IdeleGroup.infiniteComponent v
              (rationalPositiveArchimedeanIdele s) : v.Completion) ⊗ₜ[ℚ]
                (1 : K)) ⟨W, rfl⟩ =
          NumberField.LiesOver.completionMap
            (v := v) (w := W)
            (IdeleGroup.infiniteComponent v
              (rationalPositiveArchimedeanIdele s) : v.Completion)
      simpa only [map_one, mul_one] using
        (_root_.infinitePlaceTensorRingEquivAbove_tmul
          (K := ℚ) (L := K) v ⟨W, rfl⟩
          (IdeleGroup.infiniteComponent v
            (rationalPositiveArchimedeanIdele s) : v.Completion) (1 : K))
    have hlocal (W : InfinitePlace K) :
        nnnormUnitHom W.Completion
            (IdeleGroup.infiniteComponent W
              (IdeleGroup.extension ℚ K
                (rationalPositiveArchimedeanIdele s))) = s := by
      have hbelow :
          _root_.infinitePlaceBelow (K := ℚ) W = Rat.infinitePlace :=
        Subsingleton.elim _ _
      letI : W.1.LiesOver
          (_root_.infinitePlaceBelow (K := ℚ) W).1 := ⟨rfl⟩
      rw [hExtComponent W]
      calc
        nnnormUnitHom W.Completion
            (Units.map
              (NumberField.LiesOver.completionMap
                (v := _root_.infinitePlaceBelow (K := ℚ) W) (w := W))
              (IdeleGroup.infiniteComponent
                (_root_.infinitePlaceBelow (K := ℚ) W)
                (rationalPositiveArchimedeanIdele s))) =
            nnnormUnitHom
              (_root_.infinitePlaceBelow (K := ℚ) W).Completion
              (IdeleGroup.infiniteComponent
                (_root_.infinitePlaceBelow (K := ℚ) W)
                (rationalPositiveArchimedeanIdele s)) := by
          exact IdeleGroup.nnnormUnitHom_infinitePlaceCompletionMap
            (K := ℚ) (L := K)
            (_root_.infinitePlaceBelow (K := ℚ) W) W
            (IdeleGroup.infiniteComponent (_root_.infinitePlaceBelow (K := ℚ) W)
              (rationalPositiveArchimedeanIdele s))
        _ = s := by
          change nnnormUnitHom
              (_root_.infinitePlaceBelow (K := ℚ) W).Completion
              (IdeleGroup.infiniteComponent
                (_root_.infinitePlaceBelow (K := ℚ) W)
                (rationalPositiveArchimedeanIdele s)) = s
          rw [hbelow]
          exact hsource
    have harch :
        InfiniteIdeleGroup.archimedeanNorm
            (IdeleGroup.extension ℚ K
              (rationalPositiveArchimedeanIdele s)).1 = s ^ d := by
      rw [InfiniteIdeleGroup.archimedeanNorm_apply]
      apply Units.ext
      change
        (∏ W : InfinitePlace K,
          nnnormUnitHom W.Completion
              (IdeleGroup.infiniteComponent W
                (IdeleGroup.extension ℚ K
                  (rationalPositiveArchimedeanIdele s))) ^ W.mult) =
          (s ^ d : ℝ≥0)
      simp_rw [hlocal]
      have hprod :
          (∏ W : InfinitePlace K, s ^ W.mult) = s ^ d := by
        rw [Finset.prod_pow_eq_pow_sum Finset.univ
          (fun W : InfinitePlace K => W.mult) s,
          InfinitePlace.sum_mult_eq]
      exact congrArg Units.val hprod
    rw [IdeleGroup.absoluteNorm_apply, hfinite, map_one, one_mul,
      harch, hs_pow]
  have hs_value :
      rationalCyclotomicZHatIdeleValue
          (rationalPositiveArchimedeanIdele s) =
        1 := by
    rw [rationalCyclotomicZHatIdeleValue_apply,
      rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele,
      map_one]
  have hc_value :
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul c) =
        0 := by
    change
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul
            (relativeIdeleBaseChangeMulEquiv
              (K := ℚ) (L := K)
              (RelativeIdeleGroup.inclusion ℚ K
                (rationalPositiveArchimedeanIdele s)))) =
        0
    rw [normalizedCyclotomicZHatIdeleValue_baseIdeleInclusion,
      hs_value]
    simp
  refine ⟨⟨a * c, ?_⟩, ?_⟩
  · change IdeleGroup.absoluteNorm (a * c) = 1
    rw [map_mul, hc_absoluteNorm]
    simp [r]
  · change
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a + Additive.ofMul c) =
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a)
    rw [map_add, hc_value, add_zero]

end Reciprocity
end GlobalClassFieldTheory
