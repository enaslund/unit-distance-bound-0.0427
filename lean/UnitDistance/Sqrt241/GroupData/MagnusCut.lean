module

public import UnitDistance.Sqrt241.GroupData.MagnusCertificates
public import UnitDistance.Sqrt241.GroupData.MagnusFree
public import UnitDistance.Sqrt241.GroupData.Words

@[expose] public section
set_option backward.privateInPublic true


/-!
# The literal cut retains `Q_B` and detects a class of size `2^15`

For any free pro-2 group on eight generators, any continuous map `ρ` to the
retained model `Q_B` sending the generators to the elementary basis, and any
lifts `L` of the local generators whose elementary vectors are those of
construction.md §3.4 (under `ρ`):

* the closed normal closure `N` of the thirty literal cut words is killed by
  `ρ` and by the truncated Magnus cut `ψ` (with the actual cubic tails of the
  21 quadratic words);
* the image of `c₁ = L.conj 0` in the finite image of `ψ` has a centralizer of
  index at least `2^15` (`U₂ = F₂⁷`, `U₃ = F₂⁸`, conjugation vector `10111010`).

This is `magnus_retains_and_detects`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.MagnusB
open Magnus GroupData ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations

/-- Magnus initial of the tame word of norm `N`. -/
def tameInitial (q : Fin 4) : V₂ 8 Magnus.F :=
  quadraticBracket (tameInertiaVector q) (tameFrobeniusVector q) +
    (if tameNorm q % 4 = 3 then 1 else 0 : Magnus.F) • squareTensor (tameInertiaVector q)

/-- Magnus initials of the 21 quadratic words, computed from the vectors. -/
def wordInitials : Fin 21 → V₂ 8 Magnus.F :=
  ![squareTensor (conjVector 0),squareTensor (conjVector 1),tameInitial 0,tameInitial 1,
    tameInitial 2,tameInitial 3,squareTensor (dyadicYVector 1),
    squareTensor (dyadicXVector 0),quadraticBracket (dyadicXVector 0) (dyadicYVector 0),
    quadraticBracket (dyadicXVector 0) (dyadicZVector 0),
    squareTensor (dyadicXVector 1),quadraticBracket (dyadicXVector 1) (dyadicYVector 1),
    quadraticBracket (dyadicXVector 1) (dyadicZVector 1),
    squareTensor (tameInertiaVector 0),squareTensor (tameInertiaVector 1),
    squareTensor (tameInertiaVector 2),squareTensor (tameInertiaVector 3),
    squareTensor (tameFrobeniusVector 0),squareTensor (tameFrobeniusVector 1),
    squareTensor (tameFrobeniusVector 2),squareTensor (tameFrobeniusVector 3)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem wordInitials_certificate : ∀ (i : Fin 21) (j k : Fin 8), wordInitials i j k = row i j k := by
  decide +kernel

theorem wordInitials_eq (i : Fin 21) : wordInitials i = row i :=
  funext fun j => funext (wordInitials_certificate i j)

theorem tameNorm_odd (q : Fin 4) : tameNorm q % 4 = 1 ∨ tameNorm q % 4 = 3 := by
  have h : ∀ q : Fin 4, tameNorm q % 4 = 1 ∨ tameNorm q % 4 = 3 := by decide
  exact h q

theorem sq_initial (g : Group 8 Magnus.F) (v : V₁ 8 Magnus.F) (hg : g.first = v) :
    (g^2).first = 0 ∧ (g^2).second = squareTensor v := by
  rw [square_first,square_second,hg]
  exact ⟨rfl,rfl⟩

theorem comm_initial (g h : Group 8 Magnus.F) (v w : V₁ 8 Magnus.F) (hg : g.first = v)
    (hh : h.first = w) :
    (Dyadic.Presentation.comm g h).first = 0 ∧
      (Dyadic.Presentation.comm g h).second = quadraticBracket v w := by
  change (commutator g h).first = 0 ∧ (commutator g h).second = _
  rw [commutator_first,commutator_second,hg,hh]
  exact ⟨rfl,rfl⟩

theorem tame_initial (q : Fin 4) (t f : Group 8 Magnus.F) (ht : t.first = tameInertiaVector q)
    (hf : f.first = tameFrobeniusVector q) :
    (Lifts.tameWord (tameNorm q) t f).first = 0 ∧
      (Lifts.tameWord (tameNorm q) t f).second = tameInitial q := by
  have h := tameWord_odd (tameNorm q) (tameNorm_odd q) t f
  rw [ht,hf] at h
  exact h

/-- The quadratic words of lifts with the specified vectors have the 21 rows
as Magnus initials. -/
theorem quadraticWords_initials (L : Lifts (Group 8 Magnus.F)) (hL : L.Labels (fun g => g.first))
    (i : Fin 21) :
    (L.quadraticWords i).first = 0 ∧ (L.quadraticWords i).second = row i := by
  rw [← wordInitials_eq i]
  fin_cases i
  · exact sq_initial _ _ (hL.conj 0)
  · exact sq_initial _ _ (hL.conj 1)
  · exact tame_initial 0 _ _ (hL.tameInertia 0) (hL.tameFrobenius 0)
  · exact tame_initial 1 _ _ (hL.tameInertia 1) (hL.tameFrobenius 1)
  · exact tame_initial 2 _ _ (hL.tameInertia 2) (hL.tameFrobenius 2)
  · exact tame_initial 3 _ _ (hL.tameInertia 3) (hL.tameFrobenius 3)
  · exact sq_initial _ _ (hL.dyadicY 1)
  · exact sq_initial _ _ (hL.dyadicX 0)
  · exact comm_initial _ _ _ _ (hL.dyadicX 0) (hL.dyadicY 0)
  · exact comm_initial _ _ _ _ (hL.dyadicX 0) (hL.dyadicZ 0)
  · exact sq_initial _ _ (hL.dyadicX 1)
  · exact comm_initial _ _ _ _ (hL.dyadicX 1) (hL.dyadicY 1)
  · exact comm_initial _ _ _ _ (hL.dyadicX 1) (hL.dyadicZ 1)
  · exact sq_initial _ _ (hL.tameInertia 0)
  · exact sq_initial _ _ (hL.tameInertia 1)
  · exact sq_initial _ _ (hL.tameInertia 2)
  · exact sq_initial _ _ (hL.tameInertia 3)
  · exact sq_initial _ _ (hL.tameFrobenius 0)
  · exact sq_initial _ _ (hL.tameFrobenius 1)
  · exact sq_initial _ _ (hL.tameFrobenius 2)
  · exact sq_initial _ _ (hL.tameFrobenius 3)

theorem cubicWords_eq (L : Lifts (Group 8 Magnus.F)) (hL : L.Labels (fun g => g.first))
    (P : Fin 2) :
    L.cubicWords P = (⟨0,0,bracket (dyadicZVector P)
      (quadraticBracket (dyadicYVector P) (dyadicZVector P))⟩ : Group 8 Magnus.F) := by
  change commutator (commutator (L.dyadicY P) (L.dyadicZ P)) (L.dyadicZ P) = _
  rw [nested_commutator,hL.dyadicY,hL.dyadicZ]

variable {G : Type} [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {x : Fin 8 → G}

/-- The Magnus cut kills the entire closed normal cut kernel. -/
theorem closedNormalClosure_le_freeCut_ker
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (L : Lifts G)
    (hL : L.Labels (fun g => (CutData.freeDetector hfree g).first)) :
    closedNormalClosure L.words ≤
      (data.freeCut hfree (CutData.relatorTails hfree L.quadraticWords)).toMonoidHom.ker := by
  have hL' : (L.map (CutData.freeDetector hfree).toMonoidHom).Labels (fun g => g.first) :=
    Lifts.Labels.of_map _ hL
  apply closedNormalClosure_le_closed_normal
    (ProCGroups.ContinuousMonoidHom.isClosed_ker
      (data.freeCut hfree (CutData.relatorTails hfree L.quadraticWords)))
  intro g hg
  change data.freeCut hfree (CutData.relatorTails hfree L.quadraticWords) g = 1
  rcases hg with (⟨i,rfl⟩ | ⟨P,rfl⟩) | ⟨i,rfl⟩
  · apply data.freeCut_relator_eq_one hfree L.quadraticWords
    · intro k
      have hm := L.map_quadraticWords (CutData.freeDetector hfree).toMonoidHom k
      change CutData.freeDetector hfree (L.quadraticWords k) = _ at hm
      rw [hm]
      exact (quadraticWords_initials _ hL' k).1
    · intro k
      have hm := L.map_quadraticWords (CutData.freeDetector hfree).toMonoidHom k
      change CutData.freeDetector hfree (L.quadraticWords k) = _ at hm
      rw [hm]
      exact (quadraticWords_initials _ hL' k).2
  · apply data.freeCut_central_eq_one hfree _ (L.cubicWords P) _ _ (third_dyadic P)
    have hm := L.map_cubicWords (CutData.freeDetector hfree).toMonoidHom P
    change CutData.freeDetector hfree (L.cubicWords P) = _ at hm
    rw [hm]
    exact cubicWords_eq _ hL' P
  · rw [CutData.freeCut_apply,CutData.freeDetector_eq_one_of_dimension_four hfree _
      (L.deepWords_mem_dimension_four i),map_one]

/-- A single set of elementary label facts gives retention of `Q_B` and a
conjugacy class of size at least `2^15` for `c₁` in a finite quotient. -/
theorem magnus_retains_and_detects
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (ρ : G →ₜ* Retained.Q) (hρ : ∀ i, (ρ (x i)).base = Pi.single i 1)
    (L : Lifts G) (hL : L.Labels (fun g => (ρ g).base)) :
    let N := closedNormalClosure L.words
    let ψ := data.freeCut hfree (CutData.relatorTails hfree L.quadraticWords)
    N ≤ ρ.toMonoidHom.ker ∧ N ≤ ψ.toMonoidHom.ker ∧
      2^15 ≤ (Subgroup.centralizer
        ({(⟨ψ (L.conj 0),⟨L.conj 0,rfl⟩⟩ : ψ.toMonoidHom.range)} : Set ψ.toMonoidHom.range)).index := by
  have hfirst (g : G) : (CutData.freeDetector hfree g).first = (ρ g).base := by
    have hq : @Continuous G (Multiplicative (V₁ 8 Magnus.F)) _ ⊥
        ((ClassTwo.GroupModel.baseHom Retained.cocycle).comp ρ.toMonoidHom) := by
      let _ : TopologicalSpace (Multiplicative (V₁ 8 Magnus.F)) := ⊥
      exact (continuous_of_discreteTopology :
        Continuous (ClassTwo.GroupModel.baseHom Retained.cocycle)).comp ρ.continuous_toFun
    exact CutData.freeDetector_first_eq hfree _ hq (fun i => by
      apply Multiplicative.toAdd.injective
      exact hρ i) g
  have hL' : L.Labels (fun g => (CutData.freeDetector hfree g).first) := by
    simp only [hfirst]
    exact hL
  refine ⟨Retained.closedNormalClosure_le_ker ρ L hL,closedNormalClosure_le_freeCut_ker hfree L hL',?_⟩
  exact data.freeCut_image_conjugacy_index_of_first hfree _ (L.conj 0)
    ((hfirst _).trans (hL.conj 0))

end UnitDistance.Sqrt241.MagnusB
