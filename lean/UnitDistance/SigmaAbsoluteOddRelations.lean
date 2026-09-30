module

public import UnitDistance.SigmaAbsoluteLocalRestriction

@[expose] public section
set_option backward.privateInPublic true


/-! Literal odd tame relations in the fixed actual absolute local groups. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace UnitDistance.ArithmeticProP
open ArithmeticChosenGenus ArithmeticGenusFrattini

theorem sigma_absolute_odd_relation_mod (U : OpenNormalSubgroup SigmaGroup) (i : Fin 5) :
    ∃τ : SigmaOddInertia i, ∃φ : SigmaOddDecomposition i,
      sigmaGenusRestriction (sigmaOddInertiaMap i τ)=Multiplicative.ofAdd
        (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaGenusRestriction (sigmaOddDecompositionMap i φ)=Multiplicative.ofAdd
        (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaOddDecompositionMap i φ*sigmaOddInertiaMap i τ*
        (sigmaOddDecompositionMap i φ)⁻¹*
        ((sigmaOddInertiaMap i τ)^(UniversalQuadratic.oddPrimes i))⁻¹∈U := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := U ⊓ sigmaGenusOpenNormal
  let E := openNormalFiniteGaloisField ℚ maximalSigmaProTwo V
  letI : Module.Finite ℚ E := E.finiteDimensional
  letI : IsGalois ℚ E := E.isGalois
  letI : NumberField E := NumberField.of_module_finite ℚ E
  have hquot := ProCGroups.ProC.HasOpenNormalBasisInClass.quotient_mem
    (ProCGroups.FiniteGroupClass.pGroup_formation 2)
    maximalSigmaProTwo_hasPGroupOpenNormalBasis V
  let e := openNormalQuotientEquivFiniteGaloisField ℚ maximalSigmaProTwo V
  have hE : IsPGroup 2 Gal(E/ℚ) := hquot.2.of_surjective e.toMonoidHom e.surjective
  have hle : genusInMaximal≤E.toIntermediateField := by
    change genusInMaximal≤IntermediateField.fixedField (V : Subgroup SigmaGroup)
    exact (IntermediateField.le_iff_le _ _).mpr (show (V : Subgroup SigmaGroup)≤
      genusInMaximal.fixingSubgroup from inf_le_right)
  let g : GenusField →ₐ[ℚ] E :=
    (IntermediateField.inclusion hle).comp genusInMaximalEquiv.symm.toAlgHom
  let j := maximalSigmaProTwo.val.comp E.toIntermediateField.val
  obtain ⟨τ,φ,hτ,hφ,hrel⟩ := ArithmeticOdd.exists_absolute_tame_pair E g j i hE
  let r := GaloisEmbedding.restriction E.toIntermediateField.val
  have hg : E.toIntermediateField.val.comp g=sigmaGenusEmbedding := by
    ext x
    rfl
  have hsign (σ : SigmaOddDecomposition i) (v : Fin 7 → ZMod 2)
      (hv : GaloisEmbedding.restriction g
        (PrimeCompletion.decompositionRestriction (ArithmeticOdd.prime i) E j σ)=signAutomorphism v) :
      sigmaGenusRestriction (sigmaOddDecompositionMap i σ)=Multiplicative.ofAdd v := by
    apply sigmaGenusRestriction_of_action
    rw [←hg,GaloisEmbedding.restriction_comp,sigmaOddDecompositionMap_restriction]
    exact hv
  refine ⟨τ,φ,hsign τ.val _ hτ,hsign φ _ hφ,?_⟩
  let w := φ*τ.val*φ⁻¹*(τ.val^(UniversalQuadratic.oddPrimes i))⁻¹
  have hw : r (sigmaOddDecompositionMap i w)=1 := by
    rw [show r (sigmaOddDecompositionMap i w)=
      PrimeCompletion.decompositionRestriction (ArithmeticOdd.prime i) E j w from
        sigmaOddDecompositionMap_restriction i E E.toIntermediateField.val w]
    exact hrel
  have hfix : sigmaOddDecompositionMap i w∈E.toIntermediateField.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hc := GaloisEmbedding.restriction_commutes E.toIntermediateField.val
      (sigmaOddDecompositionMap i w) ⟨x,hx⟩
    change E.toIntermediateField.val (r (sigmaOddDecompositionMap i w) ⟨x,hx⟩)=
      sigmaOddDecompositionMap i w x at hc
    rw [hw] at hc
    exact hc.symm
  have hfixEq : E.toIntermediateField.fixingSubgroup=(V : Subgroup SigmaGroup) :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨(V : Subgroup SigmaGroup),V.isClosed⟩ : ClosedSubgroup SigmaGroup)
  rw [hfixEq] at hfix
  have hm := (show (V : Subgroup SigmaGroup)≤(U : Subgroup SigmaGroup) from inf_le_left) hfix
  have hmU : sigmaOddDecompositionMap i w∈U := hm
  simpa only [w,map_mul,map_inv,map_pow,sigmaOddInertiaMap_apply] using hmU

/-- Actual absolute inertia/decomposition witnesses whose images satisfy the
literal tame relation in the actual maximal arithmetic group. -/
theorem sigma_absolute_odd_relation (i : Fin 5) :
    ∃τ : SigmaOddInertia i, ∃φ : SigmaOddDecomposition i,
      sigmaGenusRestriction (sigmaOddInertiaMap i τ)=Multiplicative.ofAdd
        (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaGenusRestriction (sigmaOddDecompositionMap i φ)=Multiplicative.ofAdd
        (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaOddDecompositionMap i φ*sigmaOddInertiaMap i τ*
        (sigmaOddDecompositionMap i φ)⁻¹=
        (sigmaOddInertiaMap i τ)^(UniversalQuadratic.oddPrimes i) := by
  let f : SigmaOddInertia i × SigmaOddDecomposition i → SigmaGroup := fun x ↦
    sigmaOddDecompositionMap i x.2*sigmaOddInertiaMap i x.1*
      (sigmaOddDecompositionMap i x.2)⁻¹*((sigmaOddInertiaMap i x.1)^(UniversalQuadratic.oddPrimes i))⁻¹
  let c : SigmaOddInertia i × SigmaOddDecomposition i →
      Multiplicative (Fin 7 → ZMod 2) × Multiplicative (Fin 7 → ZMod 2) := fun x ↦
    (sigmaGenusRestriction (sigmaOddInertiaMap i x.1),
      sigmaGenusRestriction (sigmaOddDecompositionMap i x.2))
  obtain ⟨x,hx,hf⟩ := ProfiniteTame.exists_labeled_eq_one f (by fun_prop) c (by fun_prop)
    (Multiplicative.ofAdd (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)),
      Multiplicative.ofAdd (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i))) (by
      intro U
      obtain ⟨τ,φ,hτ,hφ,hrel⟩ := sigma_absolute_odd_relation_mod U i
      exact ⟨(τ,φ),Prod.ext hτ hφ,hrel⟩)
  exact ⟨x.1,x.2,congrArg Prod.fst hx,congrArg Prod.snd hx,mul_inv_eq_one.mp hf⟩

end UnitDistance.ArithmeticProP
