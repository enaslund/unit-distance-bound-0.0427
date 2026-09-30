module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section
set_option backward.privateInPublic true


/-!
# Ordered binary words and augmentation changes of basis

Changing each ordered factor `g` to `g-1` preserves the span of all binary
words. This is the successive two-by-two triangular change of basis, proved
by actual span identities in a possibly noncommutative algebra. It needs
no commuting-group assumption and no determinant oracle.
-/

noncomputable section
open scoped Pointwise
namespace UnitDistance.Jennings
variable {M : Type*} [Monoid M]

/-- The set of all ordered binary words in a list of actual monoid elements. -/
def binaryWords : List M → Set M
  | [] => {1}
  | x::xs => ({1,x} : Set M) * binaryWords xs

@[simp] theorem binaryWords_nil : binaryWords ([] : List M) = {1} := rfl
@[simp] theorem binaryWords_cons (x : M) (xs : List M) :
    binaryWords (x::xs) = ({1,x} : Set M) * binaryWords xs := rfl

/-- A specified binary choice at each position, with the original order preserved. -/
def binaryWord (xs : List M) (c : Fin xs.length → Bool) : M :=
  (List.ofFn (fun i => if c i then xs.get i else 1)).prod

@[simp] theorem binaryWord_nil (c : Fin 0 → Bool) : binaryWord ([] : List M) c = 1 := by
  simp [binaryWord]

@[simp] theorem binaryWord_cons (x : M) (xs : List M) (c : Fin (xs.length+1) → Bool) :
    binaryWord (x::xs) c = (if c 0 then x else 1) * binaryWord xs (fun i => c i.succ) := by
  simp [binaryWord, List.ofFn_succ]

/-- The coordinate-indexed family enumerates exactly all ordered binary words. -/
theorem range_binaryWord (xs : List M) : Set.range (binaryWord xs) = binaryWords xs := by
  induction xs with
  | nil =>
    ext x
    constructor
    · rintro ⟨c,rfl⟩; simp
    · rintro rfl
      exact ⟨fun i => Fin.elim0 i, by simp⟩
  | cons x xs ih =>
    ext z
    constructor
    · rintro ⟨c,rfl⟩
      rw [binaryWord_cons]
      refine ⟨(if c 0 then x else 1), ?_, binaryWord xs (fun i => c i.succ), ?_, rfl⟩
      · cases c 0 <;> simp
      · rw [← ih]
        exact ⟨_,rfl⟩
    · rintro ⟨a,ha,b,hb,rfl⟩
      rw [← ih] at hb
      obtain ⟨c,rfl⟩ := hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · refine ⟨Fin.cons false c, ?_⟩
        simp
      · refine ⟨Fin.cons true c, ?_⟩
        simp

/-- Products of independently selected factors belong to the actual word set. -/
theorem ofFn_prod_mem_binaryWords {k : ℕ} (x y : Fin k → M)
    (hy : ∀ i, y i = 1 ∨ y i = x i) : (List.ofFn y).prod ∈ binaryWords (List.ofFn x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ (f := y), List.prod_cons, List.ofFn_succ (f := x)]
    refine ⟨y 0, ?_, (List.ofFn (fun i => y i.succ)).prod, ?_, rfl⟩
    · simpa using hy 0
    · exact ih (fun i => x i.succ) (fun i => y i.succ) (fun i => hy i.succ)

theorem binaryWords_append (xs ys : List M) :
    binaryWords (xs ++ ys) = binaryWords xs * binaryWords ys := by
  induction xs with
  | nil => simp [binaryWords]
  | cons x xs ih => simp only [List.cons_append, binaryWords_cons, ih, mul_assoc]

variable {N : Type*} [Monoid N]

/-- Ordered binary-word sets commute with actual monoid homomorphisms. -/
theorem binaryWords_map (f : M →* N) (xs : List M) :
    binaryWords (xs.map f) = f '' binaryWords xs := by
  induction xs with
  | nil => simp [binaryWords]
  | cons x xs ih =>
    ext z
    constructor
    · rintro ⟨a,ha,b,hb,rfl⟩
      rw [ih] at hb
      obtain ⟨b,hb,rfl⟩ := hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨b, ⟨1, by simp, b,hb,one_mul _⟩, by simp⟩
      · exact ⟨x*b, ⟨x,by simp,b,hb,rfl⟩, by simp⟩
    · rintro ⟨z,⟨a,ha,b,hb,rfl⟩,rfl⟩
      refine ⟨f a, ?_, f b, ?_, (map_mul f a b).symm⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl
        · exact Or.inl (map_one f)
        · exact Or.inr rfl
      · rw [ih]
        exact ⟨b,hb,rfl⟩

variable (R B : Type*) [CommRing R] [Ring B] [Algebra R B]

/-- The elementary triangular two-vector change of basis. -/
theorem span_one_sub_one (x : B) :
    Submodule.span R ({1,x-1} : Set B) = Submodule.span R ({1,x} : Set B) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact Submodule.subset_span (by simp)
    · rw [hy]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact Submodule.subset_span (by simp)
    · rw [hy]
      have ht := Submodule.add_mem (Submodule.span R ({1,x-1} : Set B))
        (Submodule.subset_span (by simp : x-1 ∈ ({1,x-1} : Set B)))
        (Submodule.subset_span (by simp : (1 : B) ∈ ({1,x-1} : Set B)))
      simpa using ht

/-- Simultaneously replacing the ordered factors by their differences from
one preserves the span of all binary words, without commutativity. -/
theorem span_binaryWords_sub_one (xs : List B) :
    Submodule.span R (binaryWords (xs.map (fun x => x-1))) =
      Submodule.span R (binaryWords xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, binaryWords_cons, ← Submodule.span_mul_span,
      span_one_sub_one, ih]

end UnitDistance.Jennings
