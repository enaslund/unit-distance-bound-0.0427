module

public import UnitDistance.Sqrt241.Retained.Kernel
public import UnitDistance.Sqrt241.Retained.Concrete

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: cuts that differ only in their caps

Two families of local elements with the same complex conjugations, tame pairs and dyadic maps
differ only in their three caps. A closed normal subgroup of `F(8)` containing the cut kernel of
one and the fourth powers of the caps of the other contains the cut kernel of the other
(`kernel_le_of_same_local'`); the proof keeps both families abstract, so the kernel never
compares two concrete families field by field.

For the symmetric input `inputSym` (version 1's input with the cap `F₇²` replaced by a second
copy of `Frob(29₁)`):

* `inputSym_kernelHat_le : inputSym.kernelHat ≤ input.kernelHat`;
* `inputSym_retainedMap : inputSym.retainedMap = input.retainedMap`, hence
  `inputSym_core : inputSym.core = input.core` (the retained quotient does not see the caps).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups ProCGroups.Presentations
open _root_.UnitDistance.Sqrt241.Local

/-- **Comparison of cuts.** If `E` and `E'` have the same conjugations, tame pairs and dyadic
maps, and `N` is a closed normal subgroup of `F(8)` containing the cut kernel of `E` and the
fourth powers of the (lifted) caps of `E'`, then `N` contains the cut kernel of `E'`. -/
theorem kernel_le_of_same_local' (E E' : LocalElements) (hc : E'.conj = E.conj)
    (hi : E'.tameInertia = E.tameInertia) (hf : E'.tameFrobenius = E.tameFrobenius)
    (hd : E'.dyadic = E.dyadic) (N : Subgroup Source) [N.Normal] (hN : IsClosed (N : Set Source))
    (hEN : E.sourceLifts.kernel ≤ N)
    (hcap : ∀ k, LocalElements.lift (E'.cap k) ^ 4 ∈ N) :
    E'.sourceLifts.kernel ≤ N := by
  have hq : E'.sourceLifts.lifts.quadraticWords = E.sourceLifts.lifts.quadraticWords := by
    simp only [LocalElements.sourceLifts, SourceLifts.lifts, LocalElements.dyadicLift,
      Lifts.quadraticWords, hc, hi, hf, hd]
  have hdy : ∀ P, E'.sourceLifts.dyadic P = E.sourceLifts.dyadic P := by
    intro P
    simp only [LocalElements.sourceLifts, LocalElements.dyadicLift, hd]
  unfold SourceLifts.kernel
  apply closedNormalClosure_le_closed_normal hN
  rintro w ((⟨i, rfl⟩ | ⟨P, rfl⟩) | ⟨i, rfl⟩)
  · rw [hq]
    exact hEN (E.sourceLifts.quadratic_mem_kernel i)
  · change Dyadic.Presentation.comm (Dyadic.Presentation.comm
        (E'.sourceLifts.dyadic P Dyadic.ArithmeticPresentation.y)
        (E'.sourceLifts.dyadic P Dyadic.ArithmeticPresentation.z))
        (E'.sourceLifts.dyadic P Dyadic.ArithmeticPresentation.z) ∈ _
    rw [hdy]
    exact hEN (E.sourceLifts.cubic_mem_kernel P)
  · fin_cases i
    · change E'.sourceLifts.dyadic 0 Dyadic.ArithmeticPresentation.z ^ 4 ∈ _
      rw [hdy]
      exact hEN (E.sourceLifts.deep_mem_kernel 0)
    · change (Dyadic.Presentation.comm (E'.sourceLifts.dyadic 0 Dyadic.ArithmeticPresentation.y)
        (E'.sourceLifts.dyadic 0 Dyadic.ArithmeticPresentation.z)) ^ 2 ∈ _
      rw [hdy]
      exact hEN (E.sourceLifts.deep_mem_kernel 1)
    · change E'.sourceLifts.dyadic 1 Dyadic.ArithmeticPresentation.z ^ 4 ∈ _
      rw [hdy]
      exact hEN (E.sourceLifts.deep_mem_kernel 2)
    · change (Dyadic.Presentation.comm (E'.sourceLifts.dyadic 1 Dyadic.ArithmeticPresentation.y)
        (E'.sourceLifts.dyadic 1 Dyadic.ArithmeticPresentation.z)) ^ 2 ∈ _
      rw [hdy]
      exact hEN (E.sourceLifts.deep_mem_kernel 3)
    · exact hcap 0
    · exact hcap 1
    · exact hcap 2

/-- **Comparison of cuts**, with `N` the cut kernel of `E`. -/
theorem kernel_le_of_same_local (E E' : LocalElements) (hc : E'.conj = E.conj)
    (hi : E'.tameInertia = E.tameInertia) (hf : E'.tameFrobenius = E.tameFrobenius)
    (hd : E'.dyadic = E.dyadic)
    (hcap : ∀ k, LocalElements.lift (E'.cap k) ^ 4 ∈ E.sourceLifts.kernel) :
    E'.sourceLifts.kernel ≤ E.sourceLifts.kernel :=
  kernel_le_of_same_local' E E' hc hi hf hd _ (SourceLifts.kernel_isClosed _) le_rfl hcap

/-! ### The symmetric input -/

theorem localElements_conj : localElements.conj = ![conj₁, conj₂] := rfl
theorem localElements_tameInertia : localElements.tameInertia = tameInertia := rfl
theorem localElements_tameFrobenius : localElements.tameFrobenius = tameFrobenius := rfl
theorem localElements_dyadic : localElements.dyadic = dyadicLocal := rfl

theorem localElementsSym_conj : localElementsSym.conj = ![conj₁, conj₂] := rfl
theorem localElementsSym_tameInertia : localElementsSym.tameInertia = tameInertia := rfl
theorem localElementsSym_tameFrobenius : localElementsSym.tameFrobenius = tameFrobenius := rfl
theorem localElementsSym_dyadic : localElementsSym.dyadic = dyadicLocal := rfl

/-- The fourth power of the lift of `Frob(29_P)` is a cut word of version 1's input. -/
theorem lift_frob29_pow_four_mem (P : Fin 2) :
    LocalElements.lift (frob29 P) ^ 4 ∈ localElements.sourceLifts.kernel := by
  fin_cases P
  · exact localElements.sourceLifts.deep_mem_kernel 4
  · exact localElements.sourceLifts.deep_mem_kernel 5

theorem localElementsSym_kernel_le :
    localElementsSym.sourceLifts.kernel ≤ localElements.sourceLifts.kernel :=
  kernel_le_of_same_local localElements localElementsSym
    (localElementsSym_conj.trans localElements_conj.symm)
    (localElementsSym_tameInertia.trans localElements_tameInertia.symm)
    (localElementsSym_tameFrobenius.trans localElements_tameFrobenius.symm)
    (localElementsSym_dyadic.trans localElements_dyadic.symm)
    (fun k => by
      fin_cases k
      · exact lift_frob29_pow_four_mem 0
      · exact lift_frob29_pow_four_mem 1
      · exact lift_frob29_pow_four_mem 0)

/-- **The symmetric cut lies in version 1's cut.** -/
theorem inputSym_kernelHat_le : inputSym.kernelHat ≤ input.kernelHat := by
  rw [Input.kernelHat_eq_map, Input.kernelHat_eq_map]
  exact Subgroup.map_mono localElementsSym_kernel_le

/-- The retained map does not see the caps. -/
theorem inputSym_retainedMap : inputSym.retainedMap = input.retainedMap := by
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨s, rfl⟩ := freeMap_surjective g
  rw [Input.retainedMap_freeMap, Input.retainedMap_freeMap]

theorem inputSym_retainedKer : inputSym.retainedKer = input.retainedKer := by
  unfold Input.retainedKer
  rw [inputSym_retainedMap]

theorem inputSym_core : inputSym.core = input.core := by
  unfold Input.core
  rw [inputSym_retainedKer]

end UnitDistance.Sqrt241.Retained
