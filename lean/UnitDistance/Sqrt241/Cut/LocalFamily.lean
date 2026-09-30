module

public import UnitDistance.Sqrt241.Cut.Dyadic
public import UnitDistance.ProTwoCompletedLocalFamily
public import UnitDistance.FilteredCompletedBlockPresentation
public import UnitDistance.CyclicLocalHilbert
public import UnitDistance.OddLocalHilbert
public import UnitDistance.JenningsDyadicHilbert

@[expose] public section
set_option backward.privateInPublic true


/-!
# The local block family of the cut over `ℚ(√241)`

Blocks other than the distinguished dyadic place `𝔭₁`, indexed by
`Index = Fin 2 ⊕ Fin 4 ⊕ Unit ⊕ Fin 3`:

* two real blocks `C₂` (generator `c_i`);
* four tame blocks `C₂ × C₂ = OddLocal.D 0` (generators `τ, φ` at
  `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`);
* the ordinary dyadic block `D` at `𝔭₂` (generators `x₂, y₂, z₂`);
* three caps `C₄` (Frob(29₁), Frob(29₂), F₇²).

With `none` for `𝔭₁` this is `withDyadicIndices`. The local maps into the cut
quotient exist by the literal cut words; all their augmentation layers inject
because their composites with the retained map are the strict embeddings of
`GroupData.LocalModels` and `GroupData.DyadicMaps`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Cut
open ProCGroups ProCGroups.ProC ProCGroups.Presentations GroupData GroupAugmentation OddLocal

abbrev Index := Fin 2 ⊕ Fin 4 ⊕ Unit ⊕ Fin 3

def GeneratorType : Index → Type
  | .inl _ => Fin 1
  | .inr (.inl _) => Fin 2
  | .inr (.inr (.inl _)) => Fin 3
  | .inr (.inr (.inr _)) => Fin 1

def LocalGroup : Index → Type
  | .inl _ => Cyclic 2
  | .inr (.inl _) => OddLocal.D 0
  | .inr (.inr (.inl _)) => Dyadic.D
  | .inr (.inr (.inr _)) => Cyclic 4

instance generatorFintype (j : Index) : Fintype (GeneratorType j) := by
  rcases j with _ | _ | _ | _ <;> dsimp [GeneratorType] <;> infer_instance

instance localGroup (j : Index) : Group (LocalGroup j) := by
  rcases j with _ | _ | _ | _ <;> dsimp [LocalGroup] <;> infer_instance

instance localFinite (j : Index) : Finite (LocalGroup j) := by
  rcases j with _ | _ | _ | _ <;> dsimp [LocalGroup] <;> infer_instance

def localGenerators : ∀ j : Index, GeneratorType j → LocalGroup j
  | .inl _ => fun _ => cyclicGenerator 2
  | .inr (.inl _) => ![OddLocal.inertia 0,OddLocal.frobenius 0]
  | .inr (.inr (.inl _)) => Dyadic.Filtration.gen
  | .inr (.inr (.inr _)) => fun _ => cyclicGenerator 4

theorem localIsTwoGroup (j : Index) : IsPGroup 2 (LocalGroup j) := by
  rcases j with _ | _ | _ | _
  · exact RetainedCyclic.cyclicTwo_isTwoGroup
  · exact OddLocal.isTwoGroup 0
  · change IsPGroup 2 Dyadic.D
    exact IsPGroup.of_card (n := 5) (by rw [Nat.card_eq_fintype_card,Dyadic.D.card]; rfl)
  · exact RetainedCyclic.cyclicFour_isTwoGroup

theorem localGenerates (j : Index) : Subgroup.closure (Set.range (localGenerators j)) = ⊤ := by
  rcases j with _ | _ | _ | _
  · change Subgroup.closure (Set.range (fun _ : Fin 1 => cyclicGenerator 2)) = ⊤
    simpa using RetainedCyclic.cyclic_generates 2
  · have hr : Set.range (localGenerators (.inr (.inl ‹_›))) =
        ({OddLocal.inertia 0,OddLocal.frobenius 0} : Set (OddLocal.D 0)) := by
      ext x
      change (∃ y : Fin 2, ![OddLocal.inertia 0,OddLocal.frobenius 0] y = x) ↔ _
      simp [Fin.exists_fin_two,eq_comm]
    rw [hr]
    exact OddLocal.generators 0
  · exact dyadic_generators
  · change Subgroup.closure (Set.range (fun _ : Fin 1 => cyclicGenerator 4)) = ⊤
    simpa using RetainedCyclic.cyclic_generates 4

/-- Homomorphisms from a cyclic group agree once they agree on the generator. -/
theorem cyclic_hom_ext {H : Type*} [Group H] (n : ℕ) (f g : Cyclic n →* H)
    (h : f (cyclicGenerator n) = g (cyclicGenerator n)) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨k,rfl⟩ := cyclic_eq_generator_zpow n x
  rw [map_zpow,map_zpow,h]

/-- Canonical completed-word lifts (only used to select words). -/
def completedLift (d : ℕ) (g : FiniteFreeProTwo.Carrier d) : CompletedWords (Fin d) :=
  Function.surjInv (completionMap_surjective (FiniteFreeProTwo.generator d)
    (FiniteFreeProTwo.isFree d).generates_range) g

@[simp] theorem completedLift_map (d : ℕ) (g : FiniteFreeProTwo.Carrier d) :
    completionMap (FiniteFreeProTwo.generator d) (completedLift d g) = g :=
  Function.surjInv_eq (completionMap_surjective (FiniteFreeProTwo.generator d)
    (FiniteFreeProTwo.isFree d).generates_range) g

namespace SourceLifts
variable (A : SourceLifts)

/-- Source elements of the generators of each other block. -/
def otherSource : ∀ j : Index, GeneratorType j → Source
  | .inl i => fun _ => A.conj i
  | .inr (.inl q) => ![A.tameInertia q,A.tameFrobenius q]
  | .inr (.inr (.inl _)) => A.dyadicXYZ 1
  | .inr (.inr (.inr k)) => fun _ => A.cap k

/-! ### Relations in the quotient -/

theorem conj_square (i : Fin 2) : A.projection (A.conj i)^2 = 1 := by
  rw [← map_pow]
  fin_cases i
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 0)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 1)

theorem tameInertia_square (q : Fin 4) : A.projection (A.tameInertia q)^2 = 1 := by
  rw [← map_pow]
  fin_cases q
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 13)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 14)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 15)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 16)

theorem tameFrobenius_square (q : Fin 4) : A.projection (A.tameFrobenius q)^2 = 1 := by
  rw [← map_pow]
  fin_cases q
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 17)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 18)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 19)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 20)

theorem tameWord_eq_one (q : Fin 4) :
    A.projection (Lifts.tameWord (tameNorm q) (A.tameInertia q) (A.tameFrobenius q)) = 1 := by
  fin_cases q
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 2)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 3)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 4)
  · exact A.projection_eq_one_of_mem (A.quadratic_mem_kernel 5)

theorem tame_commute (q : Fin 4) :
    Commute (A.projection (A.tameInertia q)) (A.projection (A.tameFrobenius q)) := by
  have h := A.tameWord_eq_one q
  simp only [Lifts.tameWord,map_mul,map_inv,map_pow] at h
  have hodd : tameNorm q % 2 = 1 := by
    have hh : ∀ q : Fin 4, tameNorm q % 2 = 1 := by decide
    exact hh q
  rw [pow_eq_pow_mod _ (A.tameInertia_square q),hodd,pow_one] at h
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)).symm

theorem cap_fourth (k : Fin 3) : A.projection (A.cap k)^4 = 1 := by
  rw [← map_pow]
  fin_cases k
  · exact A.projection_eq_one_of_mem (A.deep_mem_kernel 4)
  · exact A.projection_eq_one_of_mem (A.deep_mem_kernel 5)
  · exact A.projection_eq_one_of_mem (A.deep_mem_kernel 6)

theorem tameFrobenius_residue (q : Fin 4) :
    A.projection (A.tameFrobenius q)^OddLocal.residueDegree 0 = 1 :=
  A.tameFrobenius_square q

variable (r : LocalSource) (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
  (hgen : A.Presentation r)

/-- The local maps of the other blocks into the cut quotient. -/
def otherMap : ∀ j : Index, LocalGroup j →* A.ActualQuotient
  | .inl i => cyclicMap 2 (A.projection (A.conj i)) (A.conj_square i)
  | .inr (.inl q) => OddLocal.map 0 (A.projection (A.tameInertia q))
      (A.projection (A.tameFrobenius q)) (A.tameInertia_square q) (A.tameFrobenius_residue q)
      (A.tame_commute q)
  | .inr (.inr (.inl _)) => (A.dyadicQuotientMap r hr hgen 1).toMonoidHom
  | .inr (.inr (.inr k)) => cyclicMap 4 (A.projection (A.cap k)) (A.cap_fourth k)

theorem otherMap_generator (j : Index) (i : GeneratorType j) :
    A.otherMap r hr hgen j (localGenerators j i) = A.projection (A.otherSource j i) := by
  rcases j with j | j | j | j
  · exact cyclicMap_generator 2 (A.projection (A.conj j)) (A.conj_square j)
  · fin_cases i
    · exact OddLocal.map_inertia 0 _ _ (A.tameInertia_square j) (A.tameFrobenius_residue j)
        (A.tame_commute j)
    · exact OddLocal.map_frobenius 0 _ _ (A.tameInertia_square j) (A.tameFrobenius_residue j)
        (A.tame_commute j)
  · exact A.dyadicQuotientMap_gen r hr hgen 1 i
  · exact cyclicMap_generator 4 (A.projection (A.cap j)) (A.cap_fourth j)

theorem otherMap_layers (hL : A.Labels) (j : Index) (n : ℕ) :
    Function.Injective (layerMap F (LocalGroup j) (A.otherMap r hr hgen j) n) := by
  rcases j with i | q | u | k
  · have hsq : retainedFree (A.conj i)^2 = 1 := by
      have h := congrArg (A.retained hL) (A.conj_square i)
      simpa only [map_pow,map_one,retained_projection] using h
    have he : (A.retained hL).toMonoidHom.comp (A.otherMap r hr hgen (.inl i)) =
        cyclicMap 2 (retainedFree (A.conj i)) hsq := by
      apply cyclic_hom_ext
      change A.retained hL (cyclicMap 2 (A.projection (A.conj i)) (A.conj_square i)
        (cyclicGenerator 2)) = _
      rw [cyclicMap_generator,cyclicMap_generator,retained_projection]
    exact LocalModels.layers_of_comp _ _ _ he
      (LocalModels.real_layers _ hsq i (hL.conj i)) n
  · have ht : retainedFree (A.tameInertia q)^2 = 1 := by
      have h := congrArg (A.retained hL) (A.tameInertia_square q)
      simpa only [map_pow,map_one,retained_projection] using h
    have hf : retainedFree (A.tameFrobenius q)^2 = 1 := by
      have h := congrArg (A.retained hL) (A.tameFrobenius_square q)
      simpa only [map_pow,map_one,retained_projection] using h
    have hc : Commute (retainedFree (A.tameInertia q)) (retainedFree (A.tameFrobenius q)) := by
      have h := (A.tame_commute q).map (A.retained hL)
      simpa only [retained_projection] using h
    have he : (A.retained hL).toMonoidHom.comp (A.otherMap r hr hgen (.inr (.inl q))) =
        LocalModels.tameMap Retained.cocycle _ _ ht hf hc := by
      have hi : A.otherMap r hr hgen (.inr (.inl q)) (OddLocal.inertia 0) =
          A.projection (A.tameInertia q) :=
        OddLocal.map_inertia 0 _ _ (A.tameInertia_square q) (A.tameFrobenius_residue q)
          (A.tame_commute q)
      have hfr : A.otherMap r hr hgen (.inr (.inl q)) (OddLocal.frobenius 0) =
          A.projection (A.tameFrobenius q) :=
        OddLocal.map_frobenius 0 _ _ (A.tameInertia_square q) (A.tameFrobenius_residue q)
          (A.tame_commute q)
      apply OddLocal.hom_ext
      · exact (congrArg (A.retained hL) hi).trans ((retained_projection _ _ _).trans
          (OddLocal.map_inertia 0 _ _ ht (by rw [LocalModels.residueDegree_zero]; exact hf) hc).symm)
      · exact (congrArg (A.retained hL) hfr).trans ((retained_projection _ _ _).trans
          (OddLocal.map_frobenius 0 _ _ ht (by rw [LocalModels.residueDegree_zero]; exact hf) hc).symm)
    exact LocalModels.layers_of_comp _ _ _ he
      (LocalModels.tame_layers_B _ _ ht hf hc q (hL.tameInertia q) (hL.tameFrobenius q)) n
  · exact A.dyadicQuotientMap_layers r hr hgen hL 1 n
  · have he : (A.retained hL).toMonoidHom.comp (A.otherMap r hr hgen (.inr (.inr (.inr k)))) =
        cyclicMap 4 (retainedFree (A.cap k)) (LocalModels.pow_four_eq_one Retained.cocycle _) := by
      apply cyclic_hom_ext
      change A.retained hL (cyclicMap 4 (A.projection (A.cap k)) (A.cap_fourth k)
        (cyclicGenerator 4)) = _
      rw [cyclicMap_generator,cyclicMap_generator,retained_projection]
    exact LocalModels.layers_of_comp _ _ _ he (LocalModels.cap_layers _ k (hL.cap k)) n

/-- Completed-word lifts of the generators of the other blocks. -/
def otherLifts (j : Index) (i : GeneratorType j) : CompletedWords (Fin 8) :=
  completedLift 8 (A.otherSource j i)

abbrev AllIndex := Option Index
abbrev AllGeneratorType := withDyadicIndices GeneratorType

def allGroup : AllIndex → Type
  | none => Dyadic.D
  | some j => LocalGroup j

instance allGroup_group (j : AllIndex) : Group (allGroup j) := by
  cases j <;> dsimp [allGroup] <;> infer_instance

instance allGroup_finite (j : AllIndex) : Finite (allGroup j) := by
  cases j <;> dsimp [allGroup] <;> infer_instance

def allGenerators : ∀ j : AllIndex, AllGeneratorType j → allGroup j
  | none => Dyadic.Filtration.gen
  | some j => localGenerators j

def allSource : ∀ j : AllIndex, AllGeneratorType j → Source
  | none => A.dyadicXYZ 0
  | some j => A.otherSource j

def allLifts : ∀ j : AllIndex, AllGeneratorType j → CompletedWords (Fin 8)
  | none => fun i => completedLift 8 (A.dyadicXYZ 0 i)
  | some j => A.otherLifts j

theorem allLifts_map (j : AllIndex) (i : AllGeneratorType j) :
    completionMap (FiniteFreeProTwo.generator 8) (A.allLifts j i) = A.allSource j i := by
  cases j <;> exact completedLift_map 8 _

def allMap : ∀ j : AllIndex, allGroup j →* A.ActualQuotient
  | none => (A.dyadicQuotientMap r hr hgen 0).toMonoidHom
  | some j => A.otherMap r hr hgen j

theorem allMap_generator (j : AllIndex) (i : AllGeneratorType j) :
    A.allMap r hr hgen j (allGenerators j i) = A.projection (A.allSource j i) := by
  cases j
  · exact A.dyadicQuotientMap_gen r hr hgen 0 i
  · exact A.otherMap_generator r hr hgen _ i

/-- All completed local relations of all blocks (including `𝔭₁`). -/
def allRelations : Set (CompletedWords (Fin 8)) :=
  completedGeneratorRelationFamily AllGeneratorType A.allLifts
    (completeLocalRelations AllGeneratorType allGroup allGenerators)

/-- All completed local relations of the blocks other than `𝔭₁`. -/
def otherRelations : Set (CompletedWords (Fin 8)) :=
  completedGeneratorRelationFamily GeneratorType A.otherLifts
    (completeLocalRelations GeneratorType LocalGroup localGenerators)

end SourceLifts
end UnitDistance.Sqrt241.Cut
