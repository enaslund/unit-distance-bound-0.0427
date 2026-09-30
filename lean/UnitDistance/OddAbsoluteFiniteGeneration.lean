module

public import UnitDistance.RationalLocalPairGeneration
public import UnitDistance.OddAbsoluteFinitePairs
public import UnitDistance.PadicOddIntrinsicInertiaReverse
public import UnitDistance.ArithmeticOddLocalPairs
public import UnitDistance.PadicOddGeneratingPair
public import UnitDistance.PadicOddIntrinsicInertia
public import UnitDistance.LocalInertiaFiniteImage

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite tame witnesses in the fixed rational absolute inertia and
decomposition groups, with the prescribed genus labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
open scoped NumberField ValuativeRel
namespace UnitDistance.ArithmeticOdd
open ArithmeticProP ArithmeticChosenGenus Multiquadratic
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
attribute [local instance] oddPrime PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
  (g : GenusField →ₐ[ℚ] M) (j : M →ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin 5)

/-- The actual finite odd witnesses lie in the chosen absolute local groups,
and their tame word fixes the prescribed finite rational field. -/
theorem exists_absolute_generating_tame_pair (hM : IsPGroup 2 Gal(M/ℚ)) :
    ∃τ : PrimeCompletion.AbsoluteInertia (prime i),
    ∃φ : PrimeCompletion.AbsoluteDecomposition (prime i),
      GaloisEmbedding.restriction g
        (PrimeCompletion.decompositionRestriction (prime i) M j τ.val)=
          signAutomorphism (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) ∧
      GaloisEmbedding.restriction g
        (PrimeCompletion.decompositionRestriction (prime i) M j φ)=
          signAutomorphism (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) ∧
      PrimeCompletion.decompositionRestriction (prime i) M j
        (φ*τ.val*φ⁻¹*(τ.val^(UniversalQuadratic.oddPrimes i))⁻¹)=1 ∧
      (∀x : PrimeCompletion.AbsoluteInertia (prime i), ∃n : ℤ,
        PrimeCompletion.decompositionRestriction (prime i) M j x.val=
          (PrimeCompletion.decompositionRestriction (prime i) M j τ.val)^n) ∧
      ∀y : PrimeCompletion.AbsoluteDecomposition (prime i),
        PrimeCompletion.decompositionRestriction (prime i) M j y∈
          Subgroup.closure ({PrimeCompletion.decompositionRestriction (prime i) M j τ.val,
            PrimeCompletion.decompositionRestriction (prime i) M j φ} : Set Gal(M/ℚ)) := by
  let p := prime i
  let L := LocalField M i
  let K := PrimeCompletion.Base p
  letI : Algebra ℚ_[p.val] L := by
    change Algebra ℚ_[PadicOdd.primes i]
      (RationalGaloisBaseChange.Carrier M ℚ_[PadicOdd.primes i])
    infer_instance
  letI : FiniteDimensional ℚ_[p.val] L := by
    change FiniteDimensional ℚ_[PadicOdd.primes i]
      (RationalGaloisBaseChange.Carrier M ℚ_[PadicOdd.primes i])
    infer_instance
  letI : IsGalois ℚ_[p.val] L :=
    RationalGaloisBaseChange.baseChange_galois M ℚ_[PadicOdd.primes i]
  letI : Algebra K L := PrimeCompletion.targetAlgebra p L
  letI : Module.Finite K L := PrimeCompletion.targetFinite p L
  letI : IsGalois K L := PrimeCompletion.targetGalois p L
  letI : NontriviallyNormedField L := finiteExtensionSpectralNormedField K L
  letI : IsGalois ℚ_[p.val] L := RationalGaloisBaseChange.baseChange_galois M ℚ_[PadicOdd.primes i]
  letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
  letI : IsNonarchimedeanLocalField L := finiteExtensionSpectralIsNonarchimedeanLocalField K L
  letI : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L) :=
    finiteExtensionSpectralValuation_hasExtension K L
  letI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  letI : (PadicFiniteGalois.target (PadicOdd.primes i) L).valuation.Compatible :=
    PrimeCompletion.intrinsicCompatible p L
  let fL : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let fM : M →ₐ[ℚ] SeparableClosure K :=
    fL.toRingHom.toRatAlgHom.comp (localEmbedding M i)
  obtain ⟨τL,φL,_hIgen,_hDgen,hrelL,hτL,hφL⟩ :=
    PadicOddGenus.exists_labeled_generating_tame_pair i L (localRoot M g i)
      (localRoot_sq M g i) (RationalGaloisBaseChange.isPGroup M ℚ_[PadicOdd.primes i] hM)
  let τK := (PrimeCompletion.galoisEquiv p L).symm τL.val
  let φK := (PrimeCompletion.galoisEquiv p L).symm φL
  have hτK : τK∈(galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker :=
    PadicOddGenus.inertia_mem_intrinsic i L K τL τK (fun _ ↦ rfl)
  obtain ⟨τ,hτ,hτact⟩ := exists_absoluteInertia_lift K L fL τK hτK
  obtain ⟨φ,hφ⟩ := finiteAbsoluteRestriction_surjective K L fL φK
  have hφact (x : L) : φ (fL x)=fL (φK x) := by
    rw [finiteAbsoluteRestriction_commutes,hφ]
  have hτr : GaloisEmbedding.restriction fM (τ.restrictScalars ℚ)=restriction M i τL := by
    apply GaloisEmbedding.restriction_unique
    intro x
    change fL (localEmbedding M i (restriction M i τL x))=τ (fL (localEmbedding M i x))
    rw [RationalGaloisBaseChange.restriction_commutes]
    exact (hτact (localEmbedding M i x)).symm
  have hφr : GaloisEmbedding.restriction fM (φ.restrictScalars ℚ)=restriction M i φL := by
    apply GaloisEmbedding.restriction_unique
    intro x
    change fL (localEmbedding M i (restriction M i φL x))=φ (fL (localEmbedding M i x))
    rw [RationalGaloisBaseChange.restriction_commutes]
    exact (hφact (localEmbedding M i x)).symm
  have hr (σ : Gal(SeparableClosure K/K)) :
      GaloisEmbedding.restriction fM (σ.restrictScalars ℚ)=
        restriction M i (PrimeCompletion.galoisEquiv p L (finiteAbsoluteRestriction K L fL σ)) := by
    apply GaloisEmbedding.restriction_unique
    intro x
    change fL (localEmbedding M i
        (restriction M i (PrimeCompletion.galoisEquiv p L (finiteAbsoluteRestriction K L fL σ)) x))=
      σ (fL (localEmbedding M i x))
    rw [RationalGaloisBaseChange.restriction_commutes]
    exact (finiteAbsoluteRestriction_commutes K L fL σ (localEmbedding M i x)).symm
  letI : IsMulCommutative Gal(GenusField/ℚ) := by
    refine ⟨⟨fun a b ↦ ?_⟩⟩
    apply genusGaloisEquiv.symm.injective
    rw [map_mul,map_mul,mul_comm]
  apply PrimeCompletion.exists_absolute_generating_pair_of_local_pair p M j GenusField g
    fM τ φ hτ _ _ (UniversalQuadratic.oddPrimes i)
  · rw [hτr]
    apply restriction_genus_of_localSigns
    intro k
    rw [inertia_vector]
    by_cases hk : k=PadicOdd.ramifiedIndex i
    · subst k
      simpa [binarySign,binarySignInteger] using hτL (PadicOdd.ramifiedIndex i)
    · simpa [binarySign,binarySignInteger,Pi.single_apply,hk,Ne.symm hk] using hτL k
  · rw [hφr]
    apply restriction_genus_of_localSigns
    intro k
    simpa only [binarySign,frobenius_sign_integer] using hφL k
  · change GaloisEmbedding.restriction fM (φ.restrictScalars ℚ)*
      GaloisEmbedding.restriction fM (τ.restrictScalars ℚ)*
      (GaloisEmbedding.restriction fM (φ.restrictScalars ℚ))⁻¹=
        (GaloisEmbedding.restriction fM (τ.restrictScalars ℚ))^(UniversalQuadratic.oddPrimes i)
    rw [hτr,hφr]
    simpa only [map_mul,map_inv,map_pow] using congrArg (restriction M i) hrelL
  · intro σ hσ
    let σK := finiteAbsoluteRestriction K L fL σ
    let σP := PrimeCompletion.galoisEquiv p L σK
    have hσK : σK∈(galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker :=
      finiteResidueInertia_of_absoluteInertia K L fL σ hσ σK
        (fun x ↦ finiteAbsoluteRestriction_commutes K L fL σ x)
    have hσP : σP∈PadicOddGenus.inertia i L :=
      PadicOddGenus.inertia_mem_of_intrinsic i L K σP σK (fun _ ↦ rfl) hσK
    have hz : σP∈Subgroup.zpowers τL.val := by rw [_hIgen]; exact hσP
    obtain ⟨n,hn⟩ := hz
    refine ⟨n,?_⟩
    rw [hr σ,hτr]
    simpa only [map_zpow] using congrArg (restriction M i) hn.symm
  · intro σ
    rw [hr σ,hτr,hφr]
    let σP := PrimeCompletion.galoisEquiv p L (finiteAbsoluteRestriction K L fL σ)
    have hm : σP∈Subgroup.closure ({τL.val,φL} : Set Gal(L/ℚ_[PadicOdd.primes i])) := by
      rw [_hDgen]
      trivial
    have hmap : restriction M i σP∈
        (Subgroup.closure ({τL.val,φL} : Set Gal(L/ℚ_[PadicOdd.primes i]))).map
          (restriction M i) := ⟨σP,hm,rfl⟩
    simpa only [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton] using hmap

end UnitDistance.ArithmeticOdd
