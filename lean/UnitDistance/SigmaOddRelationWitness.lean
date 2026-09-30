module

public import UnitDistance.ArithmeticOddLocalPairs
public import UnitDistance.SigmaGenusGenerators
public import UnitDistance.GaloisEmbeddingRestriction
public import UnitDistance.ProfiniteTameCompactness

@[expose] public section
set_option backward.privateInPublic true


/-! Actual genus-labeled odd tame relations in the maximal arithmetic group.
This existential result does not yet identify its chosen witnesses with
elements of a fixed absolute local decomposition/inertia subgroup. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace UnitDistance.ArithmeticProP
open ArithmeticChosenGenus ArithmeticGenusFrattini

abbrev SigmaGroup := Gal(maximalSigmaProTwo/ℚ)

def sigmaGenusEmbedding : GenusField →ₐ[ℚ] maximalSigmaProTwo :=
  genusInMaximal.val.comp genusInMaximalEquiv.symm.toAlgHom

theorem sigmaGenusRestriction_of_action (σ : SigmaGroup) (v : Fin 7 → ZMod 2)
    (h : GaloisEmbedding.restriction sigmaGenusEmbedding σ=signAutomorphism v) :
    sigmaGenusRestriction σ=Multiplicative.ofAdd v := by
  change genusGaloisEquiv.symm (AlgEquiv.autCongr genusInMaximalEquiv
    (σ.restrictNormal genusInMaximal))=Multiplicative.ofAdd v
  apply genusGaloisEquiv.injective
  rw [genusGaloisEquiv.apply_symm_apply]
  change AlgEquiv.autCongr genusInMaximalEquiv (σ.restrictNormal genusInMaximal)=signAutomorphism v
  rw [← GaloisEmbedding.restriction_subfield]
  exact h

def sigmaGenusOpenNormal : OpenNormalSubgroup SigmaGroup where
  toOpenSubgroup := ⟨genusInMaximal.fixingSubgroup,genusInMaximal.fixingSubgroup_isOpen⟩
  isNormal' := (InfiniteGalois.normal_iff_isGalois genusInMaximal).mpr inferInstance

theorem sigma_odd_relation_mod (U : OpenNormalSubgroup SigmaGroup) (i : Fin 5) :
    ∃ τ φ : SigmaGroup,
      sigmaGenusRestriction τ=Multiplicative.ofAdd
        (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaGenusRestriction φ=Multiplicative.ofAdd
        (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) ∧
      φ*τ*φ⁻¹*(τ^(UniversalQuadratic.oddPrimes i))⁻¹∈U := by
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
  obtain ⟨τE,φE,hτE,hφE,hrelE⟩ := ArithmeticOdd.exists_tame_pair E g i hE
  let r := GaloisEmbedding.restriction E.toIntermediateField.val
  obtain ⟨τ,hτ⟩ := GaloisEmbedding.restriction_surjective E.toIntermediateField.val τE
  obtain ⟨φ,hφ⟩ := GaloisEmbedding.restriction_surjective E.toIntermediateField.val φE
  have hg : E.toIntermediateField.val.comp g=sigmaGenusEmbedding := by
    ext x
    rfl
  have hsign (σ : SigmaGroup) (v : Fin 7 → ZMod 2)
      (hv : GaloisEmbedding.restriction g (r σ)=signAutomorphism v) :
      sigmaGenusRestriction σ=Multiplicative.ofAdd v := by
    apply sigmaGenusRestriction_of_action
    rw [← hg,GaloisEmbedding.restriction_comp]
    exact hv
  refine ⟨τ,φ,?_,?_,?_⟩
  · apply hsign
    change GaloisEmbedding.restriction g (GaloisEmbedding.restriction E.toIntermediateField.val τ)=_
    rw [hτ]
    exact hτE
  · apply hsign
    change GaloisEmbedding.restriction g (GaloisEmbedding.restriction E.toIntermediateField.val φ)=_
    rw [hφ]
    exact hφE
  · let w := φ*τ*φ⁻¹*(τ^(UniversalQuadratic.oddPrimes i))⁻¹
    have hw : r w=1 := by
      change GaloisEmbedding.restriction E.toIntermediateField.val
        (φ*τ*φ⁻¹*(τ^(UniversalQuadratic.oddPrimes i))⁻¹)=1
      rw [map_mul,map_mul,map_mul,map_inv,map_inv,map_pow,hτ,hφ,hrelE,mul_inv_cancel]
    have hfix : w∈E.toIntermediateField.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hc := GaloisEmbedding.restriction_commutes E.toIntermediateField.val w ⟨x,hx⟩
      change E.toIntermediateField.val (r w ⟨x,hx⟩)=w x at hc
      rw [hw] at hc
      exact hc.symm
    have hfixEq : E.toIntermediateField.fixingSubgroup=(V : Subgroup SigmaGroup) :=
      InfiniteGalois.fixingSubgroup_fixedField
        (⟨(V : Subgroup SigmaGroup),V.isClosed⟩ : ClosedSubgroup SigmaGroup)
    rw [hfixEq] at hfix
    exact (show (V : Subgroup SigmaGroup)≤(U : Subgroup SigmaGroup) from inf_le_left) hfix

/-- Actual odd relations with the prescribed seven genus coordinates.
The proof uses arithmetic finite local pairs and profinite compactness. -/
theorem sigma_odd_relation (i : Fin 5) :
    ∃ τ φ : SigmaGroup,
      sigmaGenusRestriction τ=Multiplicative.ofAdd
        (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) ∧
      sigmaGenusRestriction φ=Multiplicative.ofAdd
        (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) ∧
      φ*τ*φ⁻¹=τ^(UniversalQuadratic.oddPrimes i) :=
  ProfiniteTame.exists_tame_pair sigmaGenusRestriction _ _ _ (fun U ↦ sigma_odd_relation_mod U i)

end UnitDistance.ArithmeticProP
