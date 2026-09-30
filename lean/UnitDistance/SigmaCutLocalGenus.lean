module

public import UnitDistance.SigmaCutOdd
public import UnitDistance.SigmaCutExtraDecomposition
public import UnitDistance.SigmaCutDyadicDecomposition
public import UnitDistance.GenusLocalExclusions

@[expose] public section
set_option backward.privateInPublic true


/-! Complex conjugation is excluded by genus coordinates from every one of
the eleven finite local decomposition models in the actual cut. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups.Presentations RetainedQuadratic ClassTwo

theorem oddMap_genus_exclusion (s : Fin 5 → Source) (i : Fin 5) (g : OddLocal.D i) :
    (retained s (oddMap s i g)).base≠binaryVector 7 1 := by
  have h := DFunLike.congr_fun (oddMap_retained s i) g
  change retained s (oddMap s i g)=oddRetained i g at h
  rw [h]
  exact odd_lifts_conjugation_exclusion i _ _ g

theorem dyadicMap_genus_exclusion (s : Fin 5 → Source)
    (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
      (sigmaRelationKernel : Subgroup Source)) (g : Dyadic.D) :
    (retained s (dyadicMap s hgen g)).base≠binaryVector 7 1 := by
  have h := DFunLike.congr_fun (dyadicMap_retained s hgen) g
  change retained s (dyadicMap s hgen g)=SigmaDyadic.retainedDyadic g at h
  rw [h]
  exact dyadic_lifts_conjugation_exclusion _ _ _ g

private theorem retained_pow_base (g : RetainedQuadratic.Q) (n : ℕ) :
    (g^n).base=(n : F) • g.base := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ,GroupModel.mul_base,ih,add_smul]

theorem extraMap_genus_exclusion (i : Fin 5) (g : OddLocal.Cyclic 4) :
    (retained ExtraPrime.freeFrobenius (extraMap ExtraPrime.freeFrobenius i g)).base≠binaryVector 7 1 := by
  have h := DFunLike.congr_fun (extraMap_retained ExtraPrime.freeFrobenius i) g
  change retained ExtraPrime.freeFrobenius (extraMap ExtraPrime.freeFrobenius i g)=
    extraRetained ExtraPrime.freeFrobenius i g at h
  rw [h,extraRetained,RetainedCyclic.cyclicMap_pow_val,retained_pow_base,
    ExtraPrime.freeFrobenius_base]
  exact extra_conjugation_exclusion i _

end UnitDistance.ArithmeticProP.SigmaCut
