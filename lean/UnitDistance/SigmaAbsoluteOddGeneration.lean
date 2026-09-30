module

public import UnitDistance.SigmaAbsoluteOddRelations
public import UnitDistance.OddAbsoluteFiniteGeneration
public import UnitDistance.ProfiniteGeneratedTameCompactness

@[expose] public section
set_option backward.privateInPublic true


/-! Literal odd tame relations in the fixed actual absolute local groups. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace UnitDistance.ArithmeticProP
open ArithmeticChosenGenus ArithmeticGenusFrattini

theorem sigma_absolute_odd_generating_relation_mod (U : OpenNormalSubgroup SigmaGroup) (i : Fin 5) :
    ∃τ : SigmaOddInertia i, ∃φ : SigmaOddDecomposition i,
      sigmaGenusRestriction (sigmaOddInertiaMap i τ)=Multiplicative.ofAdd
        (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaGenusRestriction (sigmaOddDecompositionMap i φ)=Multiplicative.ofAdd
        (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaOddDecompositionMap i φ*sigmaOddInertiaMap i τ*
        (sigmaOddDecompositionMap i φ)⁻¹*
        ((sigmaOddInertiaMap i τ)^(UniversalQuadratic.oddPrimes i))⁻¹∈U ∧
      ProfiniteTame.quotientGenerates (sigmaOddInertiaMap i) (sigmaOddDecompositionMap i) U
        (sigmaOddInertiaMap i τ) (sigmaOddDecompositionMap i φ) := by
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
  obtain ⟨τ,φ,hτ,hφ,hrel,hIgen,hDgen⟩ := ArithmeticOdd.exists_absolute_generating_tame_pair E g j i hE
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
  have hfixEq : E.toIntermediateField.fixingSubgroup=(V : Subgroup SigmaGroup) :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨(V : Subgroup SigmaGroup),V.isClosed⟩ : ClosedSubgroup SigmaGroup)
  let q := QuotientGroup.mk' (U : Subgroup SigmaGroup)
  have hkernel : r.toMonoidHom.ker≤q.ker := by
    intro x hx
    have hxfix : x∈E.toIntermediateField.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro a ha
      have hc := GaloisEmbedding.restriction_commutes E.toIntermediateField.val x ⟨a,ha⟩
      change E.toIntermediateField.val (r x ⟨a,ha⟩)=x a at hc
      rw [show r x=1 from hx] at hc
      exact hc.symm
    rw [hfixEq] at hxfix
    have hxU : x∈(U : Subgroup SigmaGroup) :=
      (show (V : Subgroup SigmaGroup)≤(U : Subgroup SigmaGroup) from inf_le_left) hxfix
    exact (QuotientGroup.eq_one_iff x).mpr hxU
  refine ⟨τ,φ,hsign τ.val _ hτ,hsign φ _ hφ,?_,?_⟩
  ·
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
  · constructor
    · intro x
      obtain ⟨n,hn⟩ := hIgen x
      have hnR : r (sigmaOddInertiaMap i x)=(r (sigmaOddInertiaMap i τ))^n := by
        change GaloisEmbedding.restriction E.toIntermediateField.val (sigmaOddInertiaMap i x)=_
        rw [sigmaOddInertiaMap_apply,sigmaOddInertiaMap_apply,
          sigmaOddDecompositionMap_restriction,sigmaOddDecompositionMap_restriction]
        exact hn
      exact ⟨n,HomKernelTransfer.eq_zpow_of_eq_zpow r.toMonoidHom q hkernel
        (x:=sigmaOddInertiaMap i x) (t:=sigmaOddInertiaMap i τ) (n:=n) hnR⟩
    · intro y
      have hyR : r (sigmaOddDecompositionMap i y)∈Subgroup.closure
          ({r (sigmaOddInertiaMap i τ),r (sigmaOddDecompositionMap i φ)} : Set Gal(E/ℚ)) := by
        change GaloisEmbedding.restriction E.toIntermediateField.val (sigmaOddDecompositionMap i y)∈_
        rw [sigmaOddInertiaMap_apply,sigmaOddDecompositionMap_restriction,
          sigmaOddDecompositionMap_restriction,sigmaOddDecompositionMap_restriction]
        exact hDgen y
      have hyS : r (sigmaOddDecompositionMap i y)∈Subgroup.closure
          (r '' ({sigmaOddInertiaMap i τ,sigmaOddDecompositionMap i φ} : Set SigmaGroup)) := by
        simpa only [Set.image_insert_eq,Set.image_singleton] using hyR
      have hq := HomKernelTransfer.mem_closure_image r.toMonoidHom q hkernel
        (S:=({sigmaOddInertiaMap i τ,sigmaOddDecompositionMap i φ} : Set SigmaGroup))
        (x:=sigmaOddDecompositionMap i y) hyS
      simpa only [Set.image_insert_eq,Set.image_singleton] using hq

/-- The selected actual local pair generates both local images in every
finite quotient while satisfying the exact arithmetic tame relation. -/
theorem sigma_absolute_odd_generating_relation (i : Fin 5) :
    ∃τ : SigmaOddInertia i, ∃φ : SigmaOddDecomposition i,
      sigmaGenusRestriction (sigmaOddInertiaMap i τ)=Multiplicative.ofAdd
        (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaGenusRestriction (sigmaOddDecompositionMap i φ)=Multiplicative.ofAdd
        (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaOddDecompositionMap i φ*sigmaOddInertiaMap i τ*
        (sigmaOddDecompositionMap i φ)⁻¹=
        (sigmaOddInertiaMap i τ)^(UniversalQuadratic.oddPrimes i) ∧
      ∀U : OpenNormalSubgroup SigmaGroup,
        ProfiniteTame.quotientGenerates (sigmaOddInertiaMap i) (sigmaOddDecompositionMap i) U
          (sigmaOddInertiaMap i τ) (sigmaOddDecompositionMap i φ) := by
  letI := finitePlaceAbsoluteInertia_compactSpace ℚ
    (PrimeCompletion.place (ArithmeticOdd.prime i))
  letI := finitePlaceAbsoluteDecomposition_compactSpace ℚ
    (PrimeCompletion.place (ArithmeticOdd.prime i))
  exact ProfiniteTame.exists_generated_tame_pair (sigmaOddInertiaMap i)
    (sigmaOddDecompositionMap i) sigmaGenusRestriction sigmaGenusRestriction.continuous
    _ _ _ (fun U ↦ sigma_absolute_odd_generating_relation_mod U i)

end UnitDistance.ArithmeticProP
