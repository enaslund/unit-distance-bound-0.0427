module

public import UnitDistance.SigmaOriginalRelators
public import UnitDistance.SigmaDyadicFreeMap
public import UnitDistance.RetainedMagnusCutPresentation

@[expose] public section
set_option backward.privateInPublic true


/-! The actual twenty-seven-word global cut, with retained number-field and
finite cubic quotient diagrams derived from the constructed arithmetic lifts.
The five extra Frobenius lifts are parameters for later actual-prime choices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups ProCGroups.Presentations
open TruncatedMagnus.Certificate (presentationWords dyadicWord freeCut relatorTails)
abbrev Source := SigmaFree

def dyadicX : Source := SigmaDyadic.liftGenerator 1
def dyadicY : Source := SigmaDyadic.liftGenerator 0
def dyadicZ : Source := SigmaDyadic.liftGenerator 0*SigmaDyadic.liftGenerator 2

def quadratics : Fin 16 → Source := presentationWords sigmaFreeConjugation
  sigmaFreeOddInertia sigmaFreeOddFrobenius dyadicX dyadicY dyadicZ

def cubical : Source := dyadicWord dyadicY dyadicZ

def deep (extraFrobenius : Fin 5 → Source) : Fin 10 → Source :=
  RetainedQuadratic.Cut.deepWords dyadicY dyadicZ sigmaFreeOddFrobenius extraFrobenius

def relations (extraFrobenius : Fin 5 → Source) : Set Source :=
  Set.range quadratics ∪ {cubical} ∪ Set.range (deep extraFrobenius)

def kernel (extraFrobenius : Fin 5 → Source) : Subgroup Source :=
  closedNormalClosure (relations extraFrobenius)
instance kernel_normal (extraFrobenius : Fin 5 → Source) : (kernel extraFrobenius).Normal :=
  inferInstanceAs (closedNormalClosure _).Normal
instance kernel_closed (extraFrobenius : Fin 5 → Source) : IsClosed (kernel extraFrobenius : Set Source) :=
  closedNormalClosure_isClosed _

abbrev Quotient (extraFrobenius : Fin 5 → Source) := Source ⧸ kernel extraFrobenius

def projection (extraFrobenius : Fin 5 → Source) : Source →ₜ* Quotient extraFrobenius :=
  ⟨QuotientGroup.mk' (kernel extraFrobenius),QuotientGroup.continuous_mk⟩

theorem projection_surjective (extraFrobenius : Fin 5 → Source) :
    Function.Surjective (projection extraFrobenius) := QuotientGroup.mk'_surjective _

def cubicDetector := freeCut (FiniteFreeProTwo.isFree 7)
  (relatorTails (FiniteFreeProTwo.isFree 7) quadratics)

theorem infinity_base : (sigmaFreeRetainedMap sigmaFreeConjugation).base=
    RetainedQuadratic.Cut.vector 1 := by
  rw [sigmaFreeConjugation_base]
  have h : (Pi.single 0 1 : RetainedQuadratic.V)=RetainedQuadratic.Cut.vector 1 := by decide +kernel
  exact h

theorem inertia_base (i : Fin 5) : (sigmaFreeRetainedMap (sigmaFreeOddInertia i)).base=
    RetainedQuadratic.Cut.inertiaVector i := by
  change (sigmaRetainedModelMap (sigmaFreeMap (sigmaFreeOddInertia i))).base=_
  rw [sigmaFreeOddInertia_image,sigmaRetainedModelMap_base,sigmaOddInertia_genus]
  have h : ∀i : Fin 5,UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)=
      RetainedQuadratic.Cut.inertiaVector i := by decide +kernel
  exact h i

theorem frobenius_base (i : Fin 5) : (sigmaFreeRetainedMap (sigmaFreeOddFrobenius i)).base=
    RetainedQuadratic.Cut.frobeniusVector i := by
  change (sigmaRetainedModelMap (sigmaFreeMap (sigmaFreeOddFrobenius i))).base=_
  rw [sigmaFreeOddFrobenius_image,sigmaRetainedModelMap_base,sigmaOddFrobenius_genus]
  have h : ∀i : Fin 5,UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)=
      RetainedQuadratic.Cut.frobeniusVector i := by decide +kernel
  exact h i

theorem retained_and_cubic (extraFrobenius : Fin 5 → Source) :
    kernel extraFrobenius≤sigmaFreeRetainedMap.toMonoidHom.ker ∧
    kernel extraFrobenius≤cubicDetector.toMonoidHom.ker ∧
    4096≤(Subgroup.centralizer
      ({(⟨cubicDetector sigmaFreeConjugation,⟨sigmaFreeConjugation,rfl⟩⟩ :
          cubicDetector.toMonoidHom.range)} : Set cubicDetector.toMonoidHom.range)).index := by
  exact RetainedQuadratic.Cut.full_literal_cut_retains_and_detects
    (FiniteFreeProTwo.isFree 7) sigmaFreeRetainedMap sigmaFreeRetainedMap_generator_base
    sigmaFreeConjugation sigmaFreeOddInertia sigmaFreeOddFrobenius dyadicX dyadicY dyadicZ
    extraFrobenius infinity_base inertia_base frobenius_base
    SigmaDyadic.retained_basis_base.1 SigmaDyadic.retained_basis_base.2.1 SigmaDyadic.retained_basis_base.2.2

/-- The constructed number-field quotient descends through all twenty-seven cuts. -/
def retained (extraFrobenius : Fin 5 → Source) : Quotient extraFrobenius →ₜ* RetainedQuadratic.Q :=
  ProCGroups.QuotientGroup.liftₜ (kernel extraFrobenius) sigmaFreeRetainedMap
    (retained_and_cubic extraFrobenius).1

@[simp] theorem retained_projection (extraFrobenius : Fin 5 → Source) (g : Source) :
    retained extraFrobenius (projection extraFrobenius g)=sigmaFreeRetainedMap g := rfl

theorem retained_surjective (extraFrobenius : Fin 5 → Source) :
    Function.Surjective (retained extraFrobenius) := by
  intro q
  obtain ⟨g,hg⟩ := sigmaFreeRetainedMap_surjective q
  exact ⟨projection extraFrobenius g,hg⟩

theorem original_eq_quadratic (i : Fin 6) :
    (sigmaOriginalRelator i : Source)=quadratics ⟨i.val,by omega⟩ := by
  fin_cases i <;> rfl

theorem original_mem_kernel (extraFrobenius : Fin 5 → Source) (i : Fin 6) :
    (sigmaOriginalRelator i : Source)∈kernel extraFrobenius := by
  rw [original_eq_quadratic]
  apply subset_closedNormalClosure
  exact Or.inl (Or.inl ⟨_,rfl⟩)

end UnitDistance.ArithmeticProP.SigmaCut
