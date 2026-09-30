module

public import UnitDistance.RelativeIdealCosetsSignedReference
public import UnitDistance.RelativeUnitEnumeration
public import UnitDistance.RelativeArchimedeanCoordinates
public import UnitDistance.SIntegerPlaneProjection

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual signed-reference S-integer displacements and their unit-log enumeration -/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units
open scoped Classical nonZeroDivisors

namespace UnitDistance.RelativeIdealCosets
open RelativeUnits SIntegerCRT

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

def signedReferenceEnumeratedPoint (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (τ : torsion K) (l : differenceLattice ι) : K :=
  signedReferencePoint hι D n₀ (n, (relativeUnitEquiv ι hι hb (τ, -l)).toMul)

theorem signedReferenceEnumeratedPoint_norm (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (τ : torsion K) (l : differenceLattice ι) :
    Algebra.norm F (signedReferenceEnumeratedPoint hι hb D n₀ n τ l) = 1 :=
  signedReferencePoint_norm hι D n₀ _

theorem signedReferenceEnumeratedPoint_mem (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (τ : torsion K) (l : differenceLattice ι) :
    signedReferenceEnumeratedPoint hι hb D n₀ n τ l ∈ (Set.range D.prime).integer K :=
  signedReferencePoint_mem_sIntegers hι D n₀ _

def signedReferenceLatticeStep (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (τ : torsion K) (l : differenceLattice ι) : diagonalSIntegers D.prime :=
  diagonalEmbeddingEquiv D.prime ⟨signedReferenceEnumeratedPoint hι hb D n₀ n τ l,
    signedReferenceEnumeratedPoint_mem hι hb D n₀ n τ l⟩

@[simp] theorem signedReferenceLatticeStep_coe (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (τ : torsion K) (l : differenceLattice ι) :
    (signedReferenceLatticeStep hι hb D n₀ n τ l : EuclideanIdeal.Space K × LocalProduct D.prime) =
      (EuclideanIdeal.embedding K (signedReferenceEnumeratedPoint hι hb D n₀ n τ l),
        localEmbedding D.prime (signedReferenceEnumeratedPoint hι hb D n₀ n τ l)) := rfl

/-- Different signed labels, torsion points and log indices give different actual field steps. -/
theorem signedReferenceLatticeStep_injective (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    Function.Injective (fun p : (SignedReferenceFiber D n₀ × torsion K) × differenceLattice ι =>
      signedReferenceLatticeStep hι hb D n₀ p.1.1 p.1.2 p.2) := by
  rintro ⟨⟨n, τ⟩, l⟩ ⟨⟨n', τ'⟩, l'⟩ he
  have hp := signedReferencePoint_injective hι D n₀
    (congrArg Subtype.val ((diagonalEmbeddingEquiv D.prime).injective he))
  have hn : n = n' := congrArg Prod.fst hp
  have hu : relativeUnitEquiv ι hι hb (τ, -l) = relativeUnitEquiv ι hι hb (τ', -l') :=
    congrArg Prod.snd hp
  have ht := (relativeUnitEquiv ι hι hb).injective hu
  exact Prod.ext (Prod.ext hn (congrArg Prod.fst ht)) (neg_injective (congrArg Prod.snd ht))

theorem signedReferenceEnumeratedPoint_log (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (τ : torsion K) (l : differenceLattice ι) :
    elementDifferenceLog ι (signedReferenceEnumeratedPoint hι hb D n₀ n τ l) =
      elementDifferenceLog ι (signedReferenceGenerator hι D n₀ n : K) - (l : PairPlaceIndex F → ℝ) := by
  unfold signedReferenceEnumeratedPoint signedReferencePoint
  rw [elementDifferenceLog_mul ι (signedReferenceGenerator hι D n₀ n).ne_zero
    (NumberField.Units.coe_ne_zero _), elementDifferenceLog_unit, relativeUnitEquiv_log]
  rfl

theorem signedReferenceEnumeratedPoint_first_valuation (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (τ : torsion K) (l : differenceLattice ι) (s : S) :
    (D.prime (s, false)).valuation K (signedReferenceEnumeratedPoint hι hb D n₀ n τ l) =
      WithZero.exp (-(n.val s-n₀ s)) :=
  signedReferencePoint_first_valuation hι D n₀ _ s

theorem signedReferenceEnumeratedPoint_second_valuation (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀)
    (τ : torsion K) (l : differenceLattice ι) (s : S) :
    (D.prime (s, true)).valuation K (signedReferenceEnumeratedPoint hι hb D n₀ n τ l) =
      WithZero.exp (n.val s-n₀ s) :=
  signedReferencePoint_second_valuation hι D n₀ _ s

/-- One actual compact-place projection handles every signed reference step. -/
theorem exists_signedReferenceLatticeStep_plane (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    (D : PrimePairFamily ι S) (n₀ : S → ℤ) :
    ∃ φ : diagonalSIntegers D.prime →+ ℂ, Function.Injective φ ∧
      ∀ n τ l, ‖φ (signedReferenceLatticeStep hι hb D n₀ n τ l)‖ = 1 := by
  obtain ⟨φ, hφ, hunit⟩ := exists_sIntegerPlaneProjection ι hι hb D.prime
  refine ⟨φ, hφ, fun n τ l => ?_⟩
  exact hunit _ (signedReferenceEnumeratedPoint_norm hι hb D n₀ n τ l)

end UnitDistance.RelativeIdealCosets
