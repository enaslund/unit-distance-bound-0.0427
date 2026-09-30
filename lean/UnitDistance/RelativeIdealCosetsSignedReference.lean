module

public import UnitDistance.RelativeIdealCosetsSIntegers
public import UnitDistance.RelativeIdealCosetsUnitKernel

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual norm-one S-integer reference cosets for arbitrary signed labels -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField

namespace UnitDistance.RelativeIdealCosets

open RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S]

/-- The actual relative-class fiber of an arbitrary integer reference label.
Finite or weighted selections may restrict this type without changing the algebra. -/
abbrev SignedReferenceFiber {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (n₀ : S → ℤ) :=
  {n : S → ℤ // signedChoiceClass D n = signedChoiceClass D n₀}

def signedReferenceGenerator {ι : K ≃ₐ[F] K} (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀) : Kˣ :=
  fieldCoboundary ι (same_signedChoiceClass_exists_normOne_generator hι D n.val n₀ n.prop).choose

theorem signedReferenceGenerator_principal {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀) :
    signedStepIdeal D (n.val - n₀) =
      toPrincipalIdeal (𝓞 K) K (signedReferenceGenerator hι D n₀ n) :=
  (same_signedChoiceClass_exists_normOne_generator hι D n.val n₀ n.prop).choose_spec.1

theorem signedReferenceGenerator_norm {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀) :
    Algebra.norm F (signedReferenceGenerator hι D n₀ n : K) = 1 :=
  norm_fieldCoboundary ι hι _

theorem signedReferenceGenerator_mem_sIntegers {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀) :
    (signedReferenceGenerator hι D n₀ n : K) ∈ (Set.range D.prime).integer K :=
  signedStep_generator_mem_sIntegers D _ _ (signedReferenceGenerator_principal hι D n₀ n)

/-- An actual point in the signed reference norm-one unit coset. -/
def signedReferencePoint {ι : K ≃ₐ[F] K} (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (n₀ : S → ℤ) (p : SignedReferenceFiber D n₀ × normOneUnits (F := F) (K := K)) : K :=
  (signedReferenceGenerator hι D n₀ p.1 : K) * (p.2.val : K)

theorem signedReferencePoint_norm {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ)
    (p : SignedReferenceFiber D n₀ × normOneUnits (F := F) (K := K)) :
    Algebra.norm F (signedReferencePoint hι D n₀ p) = 1 := by
  rw [signedReferencePoint, map_mul, signedReferenceGenerator_norm, one_mul, ← coe_unitNorm,
    show unitNorm (F := F) p.2.val = 1 from p.2.prop]
  rfl

theorem signedReferencePoint_principal {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ)
    (p : SignedReferenceFiber D n₀ × normOneUnits (F := F) (K := K)) :
    signedStepIdeal D (p.1.val - n₀) = toPrincipalIdeal (𝓞 K) K
      (signedReferenceGenerator hι D n₀ p.1 * integralUnitField p.2.val) := by
  rw [map_mul, principal_integralUnitField, mul_one]
  exact signedReferenceGenerator_principal hι D n₀ p.1

theorem signedReferencePoint_mem_sIntegers {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ)
    (p : SignedReferenceFiber D n₀ × normOneUnits (F := F) (K := K)) :
    signedReferencePoint hι D n₀ p ∈ (Set.range D.prime).integer K :=
  signedStep_generator_mem_sIntegers D _ _ (signedReferencePoint_principal hι D n₀ p)

theorem signedReferencePoint_first_valuation {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ)
    (p : SignedReferenceFiber D n₀ × normOneUnits (F := F) (K := K)) (s : S) :
    (D.prime (s, false)).valuation K (signedReferencePoint hι D n₀ p) =
      WithZero.exp (-(p.1.val s - n₀ s)) :=
  signedStep_generator_first_valuation D _ _ (signedReferencePoint_principal hι D n₀ p) s

theorem signedReferencePoint_second_valuation {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ)
    (p : SignedReferenceFiber D n₀ × normOneUnits (F := F) (K := K)) (s : S) :
    (D.prime (s, true)).valuation K (signedReferencePoint hι D n₀ p) =
      WithZero.exp (p.1.val s - n₀ s) :=
  signedStep_generator_second_valuation D _ _ (signedReferencePoint_principal hι D n₀ p) s

/-- The principal ideals of the actual reference generators recover their
integer labels, so different labels cannot give the same unit coset. -/
theorem signedReferenceGenerator_principal_injective {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    Function.Injective (fun n : SignedReferenceFiber D n₀ ↦
      toPrincipalIdeal (𝓞 K) K (signedReferenceGenerator hι D n₀ n)) := by
  intro n m h
  have he := (signedReferenceGenerator_principal hι D n₀ n).trans
    (h.trans (signedReferenceGenerator_principal hι D n₀ m).symm)
  have hn := signedStepIdeal_injective D he
  apply Subtype.ext
  simpa only [sub_add_cancel] using congrArg (fun t : S → ℤ ↦ t + n₀) hn

/-- All signed reference cosets are disjoint as sets of actual field elements. -/
theorem signedReferencePoint_injective {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    Function.Injective (signedReferencePoint hι D n₀) :=
  normOneCosetPoint_injective _ (signedReferenceGenerator_principal_injective hι D n₀)

/-- The full set of norm-one generators of the prescribed signed ideal is
exactly the actual reference generator times the norm-one integral unit group. -/
theorem signedReferenceGenerator_full_fiber {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (y : Kˣ) (hy : Algebra.norm F (y : K) = 1) :
    toPrincipalIdeal (𝓞 K) K y = signedStepIdeal D (n.val - n₀) ↔
      ∃ u : normOneUnits (F := F) (K := K),
        y = signedReferenceGenerator hι D n₀ n * integralUnitField u.val := by
  rw [signedReferenceGenerator_principal]
  exact same_principal_normOne_iff _ _ (signedReferenceGenerator_norm hι D n₀ n) hy

end UnitDistance.RelativeIdealCosets
