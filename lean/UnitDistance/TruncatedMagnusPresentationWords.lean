module

public import UnitDistance.TruncatedMagnusWords
public import UnitDistance.TruncatedMagnusFree

@[expose] public section
set_option backward.privateInPublic true


/-! A literal presentation-word frontend for the actual cubic quotient.
The sixteen relations are the infinity square, five tame words, five inertia
squares, three dyadic quadratics, and two Frobenius squares. -/
noncomputable section
namespace UnitDistance.TruncatedMagnus.Certificate
open Group

def presentationWords {G : Type*} [_root_.Group G] (c : G) (t f : Fin 5 → G)
    (a b d : G) : Fin 16 → G :=
  ![c^2,
    f 0*t 0*(f 0)⁻¹*((t 0)^3)⁻¹,
    f 1*t 1*(f 1)⁻¹*((t 1)^5)⁻¹,
    f 2*t 2*(f 2)⁻¹*((t 2)^7)⁻¹,
    f 3*t 3*(f 3)⁻¹*((t 3)^11)⁻¹,
    f 4*t 4*(f 4)⁻¹*((t 4)^13)⁻¹,
    (t 0)^2,(t 1)^2,(t 2)^2,(t 3)^2,(t 4)^2,a^2,
    a⁻¹*b⁻¹*a*b,a⁻¹*d⁻¹*a*d,(f 0)^2,(f 1)^2]

def dyadicWord {G : Type*} [_root_.Group G] (b d : G) : G :=
  (b⁻¹*d⁻¹*b*d)⁻¹*d⁻¹*(b⁻¹*d⁻¹*b*d)*d

theorem map_presentationWords {G H : Type*} [_root_.Group G] [_root_.Group H]
    (π : G →* H) (c : G) (t f : Fin 5 → G) (a b d : G) (i : Fin 16) :
    π (presentationWords c t f a b d i)=
      presentationWords (π c) (fun j => π (t j)) (fun j => π (f j)) (π a) (π b) (π d) i := by
  fin_cases i <;> simp [presentationWords,map_mul,map_inv,map_pow]

theorem map_dyadicWord {G H : Type*} [_root_.Group G] [_root_.Group H]
    (π : G →* H) (b d : G) : π (dyadicWord b d)=dyadicWord (π b) (π d) := by
  simp [dyadicWord,map_mul,map_inv]

/-- Every initial is derived from the literal word and the specified elementary images. -/
theorem presentationWords_initials (c : Group F) (t f : Fin 5 → Group F) (a b d : Group F)
    (hc : c.first=vector 1)
    (ht : ∀ i,(t i).first=inertiaVector i) (hf : ∀ i,(f i).first=frobeniusVector i)
    (ha : a.first=vector 2) (hb : b.first=vector 53) (hd : d.first=vector 89)
    (i : Fin 16) :
    (presentationWords c t f a b d i).first=0 ∧
      (presentationWords c t f a b d i).second=quadraticRow i := by
  rw [← wordInitials_eq i]
  fin_cases i
  · change (c^2).first=0 ∧ (c^2).second=squareTensor (vector 1)
    rw [square_first,square_second,hc]
    exact ⟨rfl,rfl⟩
  · change (tameWord 3 (t 0) (f 0)).first=0 ∧
        (tameWord 3 (t 0) (f 0)).second=oddInitial 0
    exact tameWord_odd_initial 0 (t 0) (f 0) (ht 0) (hf 0)
  · change (tameWord 5 (t 1) (f 1)).first=0 ∧
        (tameWord 5 (t 1) (f 1)).second=oddInitial 1
    exact tameWord_odd_initial 1 (t 1) (f 1) (ht 1) (hf 1)
  · change (tameWord 7 (t 2) (f 2)).first=0 ∧
        (tameWord 7 (t 2) (f 2)).second=oddInitial 2
    exact tameWord_odd_initial 2 (t 2) (f 2) (ht 2) (hf 2)
  · change (tameWord 11 (t 3) (f 3)).first=0 ∧
        (tameWord 11 (t 3) (f 3)).second=oddInitial 3
    exact tameWord_odd_initial 3 (t 3) (f 3) (ht 3) (hf 3)
  · change (tameWord 13 (t 4) (f 4)).first=0 ∧
        (tameWord 13 (t 4) (f 4)).second=oddInitial 4
    exact tameWord_odd_initial 4 (t 4) (f 4) (ht 4) (hf 4)
  · change ((t 0)^2).first=0 ∧ ((t 0)^2).second=squareTensor (inertiaVector 0)
    rw [square_first,square_second,ht 0]
    exact ⟨rfl,rfl⟩
  · change ((t 1)^2).first=0 ∧ ((t 1)^2).second=squareTensor (inertiaVector 1)
    rw [square_first,square_second,ht 1]
    exact ⟨rfl,rfl⟩
  · change ((t 2)^2).first=0 ∧ ((t 2)^2).second=squareTensor (inertiaVector 2)
    rw [square_first,square_second,ht 2]
    exact ⟨rfl,rfl⟩
  · change ((t 3)^2).first=0 ∧ ((t 3)^2).second=squareTensor (inertiaVector 3)
    rw [square_first,square_second,ht 3]
    exact ⟨rfl,rfl⟩
  · change ((t 4)^2).first=0 ∧ ((t 4)^2).second=squareTensor (inertiaVector 4)
    rw [square_first,square_second,ht 4]
    exact ⟨rfl,rfl⟩
  · change (a^2).first=0 ∧ (a^2).second=squareTensor (vector 2)
    rw [square_first,square_second,ha]
    exact ⟨rfl,rfl⟩
  · change (commutator a b).first=0 ∧
        (commutator a b).second=quadraticBracket (vector 2) (vector 53)
    rw [commutator_first,commutator_second,ha,hb]
    exact ⟨rfl,rfl⟩
  · change (commutator a d).first=0 ∧
        (commutator a d).second=quadraticBracket (vector 2) (vector 89)
    rw [commutator_first,commutator_second,ha,hd]
    exact ⟨rfl,rfl⟩
  · change ((f 0)^2).first=0 ∧ ((f 0)^2).second=squareTensor (frobeniusVector 0)
    rw [square_first,square_second,hf 0]
    exact ⟨rfl,rfl⟩
  · change ((f 1)^2).first=0 ∧ ((f 1)^2).second=squareTensor (frobeniusVector 1)
    rw [square_first,square_second,hf 1]
    exact ⟨rfl,rfl⟩

open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations
variable {G : Type} [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {x : Fin 7 → G}

/-- The actual presentation-word kernel is killed using only elementary local images.
No quadratic-initial or cubic-tail facts are supplied as assumptions. -/
theorem literal_closedNormalClosure_le_freeCut_ker
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (c : G) (t f : Fin 5 → G) (a b d : G)
    (hc : (freeDetector hfree c).first=vector 1)
    (ht : ∀ i,(freeDetector hfree (t i)).first=inertiaVector i)
    (hf : ∀ i,(freeDetector hfree (f i)).first=frobeniusVector i)
    (ha : (freeDetector hfree a).first=vector 2)
    (hb : (freeDetector hfree b).first=vector 53)
    (hd : (freeDetector hfree d).first=vector 89)
    (deep : Set G) (hdeep : ∀ g∈deep,g∈GroupAugmentation.dimensionSubgroup F G 4) :
    closedNormalClosure (Set.range (presentationWords c t f a b d) ∪ {dyadicWord b d} ∪ deep) ≤
      (freeCut hfree (relatorTails hfree (presentationWords c t f a b d))).toMonoidHom.ker := by
  have hi (i : Fin 16) :
      (freeDetector hfree (presentationWords c t f a b d i)).first=0 ∧
      (freeDetector hfree (presentationWords c t f a b d i)).second=quadraticRow i := by
    have hm := map_presentationWords (freeDetector hfree).toMonoidHom c t f a b d i
    change freeDetector hfree (presentationWords c t f a b d i)=_ at hm
    rw [hm]
    exact presentationWords_initials _ _ _ _ _ _ hc ht hf ha hb hd i
  apply closedNormalClosure_le_freeCut_ker hfree _ (fun i => (hi i).1) (fun i => (hi i).2)
    (dyadicWord b d) _ deep hdeep
  have hm := map_dyadicWord (freeDetector hfree).toMonoidHom b d
  change freeDetector hfree (dyadicWord b d)=_ at hm
  rw [hm]
  exact nested_commutator_dyadic _ _ hb hd

end UnitDistance.TruncatedMagnus.Certificate
