module

public import UnitDistance.PadicTwoGlobalMap
public import UnitDistance.PadicTwoRootSigns
public import UnitDistance.PadicTwoQuadraticRelation
public import UnitDistance.SigmaGenusGenerators

@[expose] public section
set_option backward.privateInPublic true


/-! The actual dyadic-to-global homomorphism has the exact seven genus
coordinates used by the quadratic relation and retained dyadic model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace UnitDistance.PadicTwoGlobalMap
open Multiquadratic ArithmeticProP ArithmeticChosenGenus

/-- The actual genus embedding in the maximal global field. -/
def genusEmbedding : GenusField →ₐ[ℚ] maximalSigmaProTwo :=
  genusInMaximal.val.comp genusInMaximalEquiv.symm.toAlgHom

def globalRoot (i : Fin 7) : maximalSigmaProTwo := genusEmbedding (roots i)

theorem globalRoot_sq (i : Fin 7) : (globalRoot i)^2=(radicands i : maximalSigmaProTwo) := by
  rw [globalRoot,←map_pow,roots_sq]
  exact genusEmbedding.commutes _

theorem globalRoot_ne_zero (i : Fin 7) : globalRoot i≠0 :=
  (map_ne_zero genusEmbedding).mpr (roots_ne_zero i)

theorem globalRoot_action (σ : GlobalGroup) (i : Fin 7) :
    σ (globalRoot i)=binarySign ((sigmaGenusRestriction σ).toAdd i)*globalRoot i := by
  let τ := GaloisEmbedding.restriction genusEmbedding σ
  have he : genusGaloisEquiv (sigmaGenusRestriction σ)=τ := by
    change genusGaloisEquiv (genusGaloisEquiv.symm
      (AlgEquiv.autCongr genusInMaximalEquiv (σ.restrictNormal genusInMaximal)))=τ
    rw [genusGaloisEquiv.apply_symm_apply]
    exact (GaloisEmbedding.restriction_subfield genusInMaximal genusInMaximalEquiv σ).symm
  have h := signAutomorphism_roots (sigmaGenusRestriction σ).toAdd i
  change genusGaloisEquiv (sigmaGenusRestriction σ) (roots i)=_ at h
  rw [he] at h
  rw [globalRoot,←GaloisEmbedding.restriction_commutes genusEmbedding σ]
  change genusEmbedding (τ (roots i))=_
  rw [h,map_mul]
  simp only [binarySign,map_intCast]

def embeddedRoot (i : Fin 7) : PadicTwoMaximalProTwo.Closure :=
  globalEmbedding (globalRoot i : AlgebraicClosure ℚ)

def embeddedGlobal : maximalSigmaProTwo →ₐ[ℚ] PadicTwoMaximalProTwo.Closure :=
  globalEmbedding.comp maximalSigmaProTwo.val

def embeddedGenus : GenusField →ₐ[ℚ] PadicTwoMaximalProTwo.Closure :=
  embeddedGlobal.comp genusEmbedding

theorem embeddedRoot_sq (i : Fin 7) : (embeddedRoot i)^2=
    (PadicTwoRootSigns.globalRadicands i : PadicTwoMaximalProTwo.Closure) := by
  change (embeddedGenus (roots i))^2=_
  rw [←map_pow,roots_sq,map_ratCast]
  have he : radicands i=(PadicTwoRootSigns.globalRadicands i : ℚ) := by
    have hh : ∀i : Fin 7,radicands i=(PadicTwoRootSigns.globalRadicands i : ℚ) := by decide +kernel
    exact hh i
  rw [he,Rat.cast_intCast]

theorem embeddedRoot_ne_zero (i : Fin 7) : embeddedRoot i≠0 :=
  (map_ne_zero globalEmbedding).mpr (by exact_mod_cast globalRoot_ne_zero i)

/-- The literal sign matrix is forced by the actual four Q₂ square relations. -/
theorem absoluteMap_genus (σ : PadicTwoMaximalProTwo.AbsoluteGroup) :
    (sigmaGenusRestriction (absoluteMap σ)).toAdd=
      PadicTwoRootSigns.signsVector (PadicTwoMaximalProTwo.absoluteSigns σ).toAdd := by
  funext i
  apply binarySign_injective (E := PadicTwoMaximalProTwo.Closure)
  apply mul_right_cancel₀ (embeddedRoot_ne_zero i)
  have h := congrArg embeddedGlobal (globalRoot_action (absoluteMap σ) i)
  have hc : embeddedGlobal ((absoluteMap σ) (globalRoot i))=σ (embeddedRoot i) :=
    absoluteMap_commutes σ (globalRoot i)
  rw [hc,map_mul] at h
  simp only [binarySign,map_intCast] at h
  exact h.symm.trans (PadicTwoRootSigns.root_action σ embeddedRoot embeddedRoot_sq i)

theorem toGlobal_genus (g : PadicTwoMaximalProTwo.Group) :
    (sigmaGenusRestriction (toGlobal g)).toAdd=
      PadicTwoRootSigns.signsVector (PadicTwoMaximalProTwo.signs g).toAdd := by
  obtain ⟨σ,rfl⟩ := PadicTwoMaximalProTwo.projection_surjective g
  exact absoluteMap_genus σ

/-- The chosen local (a,b,c) generators have global masks (53,2,108). -/
theorem localGenerator_genus (i : Fin 3) :
    (sigmaGenusRestriction (toGlobal (PadicTwoQuadraticRelation.generator i))).toAdd=
      RetainedQuadratic.binaryVector 7 (![53,2,108] i) := by
  rw [toGlobal_genus,PadicTwoQuadraticRelation.generator_signs]
  have h : ∀i : Fin 3,PadicTwoRootSigns.signsVector (Pi.single i 1)=
      RetainedQuadratic.binaryVector 7 (![53,2,108] i) := by decide +kernel
  exact h i

/-- The basis (x,y,z)=(b,a,a*c) has exactly the retained dyadic masks. -/
theorem retained_basis_genus :
    (sigmaGenusRestriction (toGlobal (PadicTwoQuadraticRelation.generator 1))).toAdd=
      RetainedQuadratic.binaryVector 7 2 ∧
    (sigmaGenusRestriction (toGlobal (PadicTwoQuadraticRelation.generator 0))).toAdd=
      RetainedQuadratic.binaryVector 7 53 ∧
    (sigmaGenusRestriction (toGlobal
      (PadicTwoQuadraticRelation.generator 0*PadicTwoQuadraticRelation.generator 2))).toAdd=
      RetainedQuadratic.binaryVector 7 89 := by
  refine ⟨localGenerator_genus 1,localGenerator_genus 0,?_⟩
  rw [map_mul,map_mul]
  change (sigmaGenusRestriction (toGlobal (PadicTwoQuadraticRelation.generator 0))).toAdd+
    (sigmaGenusRestriction (toGlobal (PadicTwoQuadraticRelation.generator 2))).toAdd=_
  rw [localGenerator_genus,localGenerator_genus]
  have h : RetainedQuadratic.binaryVector 7 53+RetainedQuadratic.binaryVector 7 108=
      RetainedQuadratic.binaryVector 7 89 := by decide +kernel
  exact h

end UnitDistance.PadicTwoGlobalMap
