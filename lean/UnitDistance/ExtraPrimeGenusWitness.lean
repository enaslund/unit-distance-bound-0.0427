module

public import UnitDistance.ExtraPrimeGenusAction
public import UnitDistance.RationalGaloisBaseChange
public import UnitDistance.RationalLocalPairTransfer
public import UnitDistance.SigmaOddRelationWitness
public import UnitDistance.SigmaUnramifiedFrobenius

@[expose] public section
set_option backward.privateInPublic true


/-! Actual chosen decomposition groups at the five extra primes contain the
Euler-sign elements, proved by finite local base change and Galois restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace UnitDistance.ExtraPrime
open ArithmeticChosenGenus ArithmeticProP Multiquadratic PrimeCompletion
attribute [local instance] primeFact PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
  (g : GenusField →ₐ[ℚ] M) (i : Fin 5)
abbrev LocalField := RationalGaloisBaseChange.Carrier M ℚ_[primes i]
abbrev localEmbedding := RationalGaloisBaseChange.embedding M ℚ_[primes i]
def localRoot (j : Fin 7) : LocalField M i := localEmbedding M i (g (roots j))

theorem localRoot_sq (j : Fin 7) :
    (localRoot M g i j)^2=(radicands j : LocalField M i) := by
  rw [localRoot,←map_pow,←map_pow,roots_sq,map_ratCast,map_ratCast]
  have he : ∀k : Fin 7, ArithmeticChosenGenus.radicands k=(radicands k : ℚ) := by decide +kernel
  rw [he]
  norm_cast

theorem sign_integer (j : Fin 7) :
    binarySignInteger (vector i j)=residueSign i j := by
  have h : ∀i : Fin 5,∀j : Fin 7,binarySignInteger (vector i j)=residueSign i j := by decide +kernel
  exact h i j

theorem restriction_genus_of_localSigns
    (σ : Gal(LocalField M i/ℚ_[primes i]))
    (hσ : ∀j,σ (localRoot M g i j)=(residueSign i j : LocalField M i)*localRoot M g i j) :
    GaloisEmbedding.restriction g (RationalGaloisBaseChange.restriction M ℚ_[primes i] σ)=
      signAutomorphism (vector i) := by
  apply automorphism_ext_roots
  intro j
  apply g.injective
  apply (localEmbedding M i).injective
  change localEmbedding M i (g (GaloisEmbedding.restriction g
    (RationalGaloisBaseChange.restriction M ℚ_[primes i] σ) (roots j)))=
      localEmbedding M i (g (signAutomorphism (vector i) (roots j)))
  rw [GaloisEmbedding.restriction_commutes,RationalGaloisBaseChange.restriction_commutes]
  rw [signAutomorphism_roots,map_mul,map_mul]
  simpa only [binarySign,sign_integer,map_intCast,localRoot,localEmbedding] using hσ j

private instance genusGalCommutative : IsMulCommutative Gal(GenusField/ℚ) := by
  refine ⟨⟨fun a b ↦ ?_⟩⟩
  apply genusGaloisEquiv.symm.injective
  rw [map_mul,map_mul,mul_comm]

/-- A Frobenius with the exact seven Euler signs belongs to the chosen actual
absolute decomposition subgroup, for every actual finite Galois field
containing the genus field and every embedding in the global closure. -/
theorem exists_labeled_decomposition (j : M →ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃d : AbsoluteDecomposition (prime i),
      GaloisEmbedding.restriction g (decompositionRestriction (prime i) M j d)=
        signAutomorphism (vector i) := by
  let p := prime i
  let L := LocalField M i
  let K := Base p
  letI : Algebra ℚ_[p.val] L := by
    change Algebra ℚ_[primes i]
      (RationalGaloisBaseChange.Carrier M ℚ_[primes i])
    infer_instance
  letI : FiniteDimensional ℚ_[p.val] L := by
    change FiniteDimensional ℚ_[primes i]
      (RationalGaloisBaseChange.Carrier M ℚ_[primes i])
    infer_instance
  letI : IsGalois ℚ_[p.val] L := RationalGaloisBaseChange.baseChange_galois M ℚ_[primes i]
  letI : Algebra K L := PrimeCompletion.targetAlgebra p L
  letI : IsGalois K L := PrimeCompletion.targetGalois p L
  let fL : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let fM : M →ₐ[ℚ] SeparableClosure K :=
    fL.toRingHom.toRatAlgHom.comp (localEmbedding M i)
  obtain ⟨φL,hφL⟩ := exists_frobenius_signs i L (localRoot M g i) (localRoot_sq M g i)
  let φK := (PrimeCompletion.galoisEquiv p L).symm φL
  obtain ⟨φ,hφ⟩ := GaloisEmbedding.restriction_surjective fL φK
  have hφact (x : L) : φ (fL x)=fL (φK x) := by
    rw [←GaloisEmbedding.restriction_commutes,hφ]
  have hr : GaloisEmbedding.restriction fM (φ.restrictScalars ℚ)=
      RationalGaloisBaseChange.restriction M ℚ_[primes i] φL := by
    apply GaloisEmbedding.restriction_unique
    intro x
    change fL (localEmbedding M i (RationalGaloisBaseChange.restriction M ℚ_[primes i] φL x))=
      φ (fL (localEmbedding M i x))
    rw [RationalGaloisBaseChange.restriction_commutes]
    exact (hφact (localEmbedding M i x)).symm
  let d := (decompositionEquiv p).symm φ
  refine ⟨d,?_⟩
  rw [decomposition_label_independent p M j GenusField g fM]
  rw [show decompositionEquiv p d=φ from (decompositionEquiv p).apply_symm_apply φ,hr]
  exact restriction_genus_of_localSigns M g i φL hφL


/-- The image in the actual maximal six-prime extension has the seven
arithmetically computed genus coordinates. -/
theorem exists_labeled_sigma_decomposition (i : Fin 5) :
    ∃d : AbsoluteDecomposition (prime i),
      sigmaGenusRestriction (SigmaUnramified.decompositionMap (prime i) d)=
        Multiplicative.ofAdd (vector i) := by
  let j : GenusField →ₐ[ℚ] AlgebraicClosure ℚ := maximalSigmaProTwo.val.comp sigmaGenusEmbedding
  obtain ⟨d,hd⟩ := exists_labeled_decomposition GenusField (AlgHom.id ℚ GenusField) i j
  have hid : GaloisEmbedding.restriction (AlgHom.id ℚ GenusField)
      (decompositionRestriction (prime i) GenusField j d)=decompositionRestriction (prime i) GenusField j d :=
    GaloisEmbedding.restriction_unique _ _ _ (fun _ => rfl)
  rw [hid] at hd
  refine ⟨d,sigmaGenusRestriction_of_action _ _ ?_⟩
  rw [←hd]
  apply GaloisEmbedding.restriction_unique
  intro x
  apply maximalSigmaProTwo.val.injective
  change j (decompositionRestriction (prime i) GenusField j d x)=
    (absoluteToMaximalProPOutside 2 sigmaPrimeSupport d.val (sigmaGenusEmbedding x) : AlgebraicClosure ℚ)
  rw [absoluteToMaximalProPOutside_apply]
  exact GaloisEmbedding.restriction_commutes j d.val x

end UnitDistance.ExtraPrime
