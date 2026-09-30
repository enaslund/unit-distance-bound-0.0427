module

public import UnitDistance.Sqrt241.GroupData.MagnusGroup
public import UnitDistance.TruncatedMagnusConjugacyIndex
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option backward.privateInPublic true


/-!
# Large conjugacy classes in truncated Magnus cut quotients

Generalization of `TruncatedMagnusLinear`, `TruncatedMagnusConjugacy` and
`TruncatedMagnusConjugacyFlexible` (ℚ: seven generators, conjugation vector
`e₀`, sixteen rows, `2^12`) to certificate data `CutData n m a b`:

* `m` quadratic rows with a left inverse (so arbitrary cubic tails of the
  relators can be retained);
* a second-layer detector `U₂ = F₂^a` killing the rows and dual to the
  brackets `[e_{baseIndex i}, c]`;
* a third-layer detector `U₃ = F₂^b` killing all brackets `[e_j, row]` and
  dual to `[c, [e_p, e_q]]` for `b` selected generator pairs.

Then for every element `c` with elementary vector `cVec`, the conjugates of
`c` by `2^(a+b)` explicit words stay distinct in the cut quotient, for any
cubic tails; hence the centralizer of `c` has index at least `2^(a+b)` in
every subgroup containing the generators.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.Sqrt241.Magnus
open _root_.UnitDistance.Sqrt241.Magnus.Group ClassTwo.Collection
abbrev F := ZMod 2
variable {n : ℕ}

def e (i : Fin n) : V₁ n F := Pi.single i 1

def quadraticBracket (x y : V₁ n F) : V₂ n F := fun i j => x i*y j-y i*x j

def squareTensor (x : V₁ n F) : V₂ n F := fun i j => x i*x j

theorem quadraticBracket_comm (x y : V₁ n F) : quadraticBracket x y = quadraticBracket y x := by
  ext i j
  simp [quadraticBracket,sub_eq_add_neg,ZMod.neg_eq_self_mod_two,add_comm]

def coordinateCombination {m : ℕ} {W : Type*} [AddCommGroup W] [Module F W]
    (w : Fin m → W) : (Fin m → F) →ₗ[F] W where
  toFun v := ∑ i, v i • w i
  map_add' v u := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

@[simp] theorem coordinateCombination_single {m : ℕ} {W : Type*} [AddCommGroup W]
    [Module F W] (w : Fin m → W) (i : Fin m) :
    coordinateCombination w (Pi.single i (1 : F)) = w i := by
  classical
  simp [coordinateCombination,Pi.single_apply]

def bracketLinear : V₁ n F →ₗ[F] V₂ n F →ₗ[F] V₃ n F where
  toFun x :=
    { toFun := bracket x
      map_add' y z := by ext i j k; simp [bracket]; ring
      map_smul' r y := by ext i j k; simp [bracket,smul_eq_mul]; ring }
  map_add' x y := by ext z i j k; simp [bracket]; ring
  map_smul' r x := by ext z i j k; simp [bracket,smul_eq_mul]; ring

@[simp] theorem bracketLinear_apply (x : V₁ n F) (y : V₂ n F) :
    bracketLinear x y = bracket x y := rfl

def quadraticBracketLeft (c : V₁ n F) : V₁ n F →ₗ[F] V₂ n F where
  toFun x := quadraticBracket x c
  map_add' x y := by ext i j; simp [quadraticBracket]; ring
  map_smul' r x := by ext i j; simp [quadraticBracket,smul_eq_mul]; ring

theorem linearMap_ext_single {m : ℕ} {M : Type*} [AddCommGroup M] [Module F M]
    {f g : (Fin m → F) →ₗ[F] M} (h : ∀ j, f (Pi.single j 1) = g (Pi.single j 1)) : f = g := by
  apply (Pi.basisFun F (Fin m)).ext
  intro j
  simpa only [Pi.basisFun_apply] using h j

/-- Certificate data for a truncated Magnus cut with a conjugation vector. -/
structure CutData (n m a b : ℕ) where
  row : Fin m → V₂ n F
  leftInverse : V₂ n F →ₗ[F] (Fin m → F)
  second : V₂ n F →ₗ[F] (Fin a → F)
  third : V₃ n F →ₗ[F] (Fin b → F)
  baseIndex : Fin a → Fin n
  pairs : Fin b → Fin n × Fin n
  cVec : V₁ n F
  leftInverse_row : ∀ i, leftInverse (row i) = Pi.single i 1
  second_row : ∀ i, second (row i) = 0
  third_row : ∀ i j, third (bracket (e j) (row i)) = 0
  second_detect : ∀ i, second (quadraticBracket (e (baseIndex i)) cVec) = Pi.single i 1
  third_detect : ∀ i,
    third (bracket cVec (quadraticBracket (e (pairs i).1) (e (pairs i).2))) = Pi.single i 1

namespace CutData
variable {m a b : ℕ} (C : CutData n m a b)

def rowMap : (Fin m → F) →ₗ[F] V₂ n F := coordinateCombination C.row

def selectedQuadratic (i : Fin b) : V₂ n F :=
  quadraticBracket (e (C.pairs i).1) (e (C.pairs i).2)

def selectedMap : (Fin b → F) →ₗ[F] V₂ n F := coordinateCombination C.selectedQuadratic

def baseMap : (Fin a → F) →ₗ[F] V₁ n F := coordinateCombination (fun i => e (C.baseIndex i))

theorem leftInverse_rowMap (v : Fin m → F) : C.leftInverse (C.rowMap v) = v := by
  have h : C.leftInverse.comp C.rowMap = LinearMap.id := by
    apply linearMap_ext_single
    intro i
    simp only [LinearMap.comp_apply,LinearMap.id_apply,rowMap,coordinateCombination_single]
    exact C.leftInverse_row i
  exact congrArg (fun f : (Fin m → F) →ₗ[F] (Fin m → F) => f v) h

theorem second_rowMap (v : Fin m → F) : C.second (C.rowMap v) = 0 := by
  have h : C.second.comp C.rowMap = 0 := by
    apply linearMap_ext_single
    intro i
    simp only [LinearMap.comp_apply,LinearMap.zero_apply,rowMap,coordinateCombination_single]
    exact C.second_row i
  exact congrArg (fun f : (Fin m → F) →ₗ[F] (Fin a → F) => f v) h

theorem third_bracket_rowMap (x : V₁ n F) (v : Fin m → F) :
    C.third (bracket x (C.rowMap v)) = 0 := by
  have h (i : Fin n) : C.third.comp ((bracketLinear (e i)).comp C.rowMap) = 0 := by
    apply linearMap_ext_single
    intro j
    simp only [LinearMap.comp_apply,LinearMap.zero_apply,rowMap,coordinateCombination_single,
      bracketLinear_apply]
    exact C.third_row j i
  have h' : C.third.comp (bracketLinear.flip (C.rowMap v)) = 0 := by
    apply linearMap_ext_single
    intro i
    simpa only [LinearMap.comp_apply,LinearMap.flip_apply,LinearMap.zero_apply,
      bracketLinear_apply,e] using congrArg (fun f : (Fin m → F) →ₗ[F] (Fin b → F) => f v) (h i)
  exact congrArg (fun f : V₁ n F →ₗ[F] (Fin b → F) => f x) h'

theorem third_bracket_selectedMap (v : Fin b → F) :
    C.third (bracket C.cVec (C.selectedMap v)) = v := by
  have h : C.third.comp ((bracketLinear C.cVec).comp C.selectedMap) = LinearMap.id := by
    apply linearMap_ext_single
    intro i
    simp only [LinearMap.comp_apply,LinearMap.id_apply,selectedMap,coordinateCombination_single,
      bracketLinear_apply]
    exact C.third_detect i
  exact congrArg (fun f : (Fin b → F) →ₗ[F] (Fin b → F) => f v) h

theorem second_bracket_baseMap (u : Fin a → F) :
    C.second (quadraticBracket (C.baseMap u) C.cVec) = u := by
  have h : C.second.comp ((quadraticBracketLeft C.cVec).comp C.baseMap) = LinearMap.id := by
    apply linearMap_ext_single
    intro i
    simp only [LinearMap.comp_apply,LinearMap.id_apply,baseMap,coordinateCombination_single]
    exact C.second_detect i
  exact congrArg (fun f : (Fin a → F) →ₗ[F] (Fin a → F) => f u) h

/-- Arbitrary cubic tails of the relators are retained in the defining condition. -/
def tailCorrection (tails : Fin m → V₃ n F) : V₂ n F →ₗ[F] (Fin b → F) :=
  C.third.comp ((coordinateCombination tails).comp C.leftInverse)

def cutSubgroup (tails : Fin m → V₃ n F) : Subgroup (Group n F) :=
  relationSubgroup (LinearMap.range C.rowMap) C.third (C.tailCorrection tails)

instance cutSubgroup_normal (tails : Fin m → V₃ n F) : (C.cutSubgroup tails).Normal :=
  relationSubgroup_normal _ _ _ (by
    intro x y hy
    obtain ⟨v,rfl⟩ := hy
    exact C.third_bracket_rowMap x v)

/-- Every quadratic relator with its actual cubic tail lies in the cut subgroup. -/
theorem relator_mem_cutSubgroup (tails : Fin m → V₃ n F) (i : Fin m) :
    (⟨0,C.row i,tails i⟩ : Group n F) ∈ C.cutSubgroup tails := by
  apply relation_mem
  · exact ⟨Pi.single i 1,coordinateCombination_single _ i⟩
  · change C.third (tails i) = C.third (coordinateCombination tails (C.leftInverse (C.row i)))
    rw [C.leftInverse_row i,coordinateCombination_single]

theorem central_mem_cutSubgroup (tails : Fin m → V₃ n F) (z : V₃ n F) (hz : C.third z = 0) :
    (⟨0,0,z⟩ : Group n F) ∈ C.cutSubgroup tails :=
  (central_mem_relationSubgroup _ _ _ _).mpr hz

abbrev Cut (tails : Fin m → V₃ n F) := Group n F ⧸ C.cutSubgroup tails

def quotientMap (tails : Fin m → V₃ n F) : Group n F →* C.Cut tails :=
  QuotientGroup.mk' (C.cutSubgroup tails)

section GenericRing
variable {R : Type*} [CommRing R]

theorem conjugate_second (g h : Group n R) :
    (g*h*g⁻¹).second = fun i j => h.second i j+g.first i*h.first j-h.first i*g.first j := by
  ext i j
  simp
  ring

theorem conjugate_of_first_zero (g h : Group n R) (hg : g.first = 0) :
    g*h*g⁻¹ = (⟨h.first,h.second,h.third-bracket h.first g.second⟩ : Group n R) := by
  ext <;> simp [hg,bracket]
  ring

theorem div_second_of_first_eq (g h : Group n R) (hf : g.first = h.first) :
    (g/h).second = g.second-h.second := by
  ext i j
  simp [div_eq_mul_inv,hf]
  ring

theorem div_third_of_first_second_eq (g h : Group n R)
    (hf : g.first = h.first) (hs : g.second = h.second) : (g/h).third = g.third-h.third := by
  ext i j k
  simp [div_eq_mul_inv,hf,hs]
  ring

end GenericRing

theorem second_eq_of_quotient (tails : Fin m → V₃ n F) (g h : Group n F)
    (hf : g.first = h.first) (he : C.quotientMap tails g = C.quotientMap tails h) :
    C.second g.second = C.second h.second := by
  have hm : g/h ∈ C.cutSubgroup tails := QuotientGroup.eq_iff_div_mem.mp he
  obtain ⟨v,hv⟩ := hm.2.1
  have hz : C.second (g/h).second = 0 := by
    rw [← hv]
    exact C.second_rowMap v
  rw [div_second_of_first_eq g h hf,map_sub,sub_eq_zero] at hz
  exact hz

theorem third_eq_of_quotient (tails : Fin m → V₃ n F) (g h : Group n F)
    (hf : g.first = h.first) (hs : g.second = h.second)
    (he : C.quotientMap tails g = C.quotientMap tails h) :
    C.third g.third = C.third h.third := by
  have hm : g/h ∈ C.cutSubgroup tails := QuotientGroup.eq_iff_div_mem.mp he
  have hz := hm.2.2
  rw [div_second_of_first_eq g h hf,hs,sub_self,map_zero,
    div_third_of_first_second_eq g h hf hs,map_sub,sub_eq_zero] at hz
  exact hz

/-! ### Conjugating words -/

/-- Free-generator images in the truncated group. -/
def generator (i : Fin n) : Group n F := ⟨e i,0,0⟩

theorem bit_first (g : Group n F) (t : F) : (bit g t).first = t • g.first := by
  rcases binary_cases t with rfl | rfl <;> simp

theorem bit_second (g : Group n F) (t : F) : (bit g t).second = t • g.second := by
  rcases binary_cases t with rfl | rfl <;> simp

theorem word_first {ι : Type*} (g : ι → Group n F) (l : List ι) (v : ι → F) :
    (word g l v).first = (l.map fun i => v i • (g i).first).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [word_cons,mul_first,bit_first,ih,List.map_cons,List.sum_cons]

theorem word_second_of_first {ι : Type*} (g : ι → Group n F) (l : List ι) (v : ι → F)
    (hg : ∀ i, (g i).first = 0) :
    (word g l v).second = (l.map fun i => v i • (g i).second).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [word_cons,List.map_cons,List.sum_cons,← ih]
    ext j k
    simp [bit_first,hg]
    rw [bit_second]
    rfl

def baseWord (u : Fin a → F) : Group n F :=
  word (fun i : Fin a => generator (C.baseIndex i)) (List.finRange a) u

def quadraticGenerator (i : Fin b) : Group n F :=
  generator (C.pairs i).1*generator (C.pairs i).2*
    (generator (C.pairs i).1)⁻¹*(generator (C.pairs i).2)⁻¹

def quadraticWord (v : Fin b → F) : Group n F :=
  word C.quadraticGenerator (List.finRange b) v

@[simp] theorem quadraticGenerator_first (i : Fin b) : (C.quadraticGenerator i).first = 0 := by
  simp [quadraticGenerator]

theorem quadraticGenerator_second (i : Fin b) :
    (C.quadraticGenerator i).second = C.selectedQuadratic i := by
  funext j k
  simpa only [quadraticGenerator,generator,selectedQuadratic,quadraticBracket] using
    Group.commutator_second (generator (C.pairs i).1) (generator (C.pairs i).2) j k

theorem baseWord_first (u : Fin a → F) : (C.baseWord u).first = C.baseMap u := by
  rw [baseWord,word_first,← Fin.sum_univ_def]
  rfl

theorem quadraticWord_first (v : Fin b → F) : (C.quadraticWord v).first = 0 := by
  rw [quadraticWord,word_first]
  simp

theorem quadraticWord_second (v : Fin b → F) :
    (C.quadraticWord v).second = C.selectedMap v := by
  rw [quadraticWord,word_second_of_first _ _ _ C.quadraticGenerator_first,← Fin.sum_univ_def]
  simp only [quadraticGenerator_second]
  rfl

def conjugator (u : Fin a → F) (v : Fin b → F) : Group n F := C.baseWord u*C.quadraticWord v

def conjugateOf (c : Group n F) (u : Fin a → F) (v : Fin b → F) : Group n F :=
  C.conjugator u v*c*(C.conjugator u v)⁻¹

theorem conjugateOf_second_detect (c : Group n F) (hc : c.first = C.cVec) (u : Fin a → F)
    (v : Fin b → F) :
    C.second (C.conjugateOf c u v).second = C.second c.second+u := by
  have h : (C.conjugateOf c u v).second = c.second+quadraticBracket (C.baseMap u) C.cVec := by
    rw [conjugateOf,conjugate_second]
    ext i j
    simp only [conjugator,mul_first,baseWord_first,quadraticWord_first,hc,
      quadraticBracket,Pi.add_apply,Pi.zero_apply,add_zero]
    ring
  rw [h,map_add,second_bracket_baseMap]

theorem quadratic_conjugateOf_third_detect (c : Group n F) (hc : c.first = C.cVec)
    (v : Fin b → F) :
    C.third (C.quadraticWord v*c*(C.quadraticWord v)⁻¹).third = C.third c.third-v := by
  rw [conjugate_of_first_zero _ _ (C.quadraticWord_first v)]
  change C.third (c.third-bracket c.first (C.quadraticWord v).second) = _
  rw [map_sub,hc,quadraticWord_second,third_bracket_selectedMap]

/-- The conjugates by the `2^(a+b)` words are distinct in the cut quotient. -/
theorem conjugateOf_injective (tails : Fin m → V₃ n F) (c : Group n F) (hc : c.first = C.cVec) :
    Function.Injective (fun p : (Fin a → F) × (Fin b → F) =>
      C.quotientMap tails (C.conjugateOf c p.1 p.2)) := by
  intro p q hpq
  have hu : p.1 = q.1 := by
    have h := C.second_eq_of_quotient tails (C.conjugateOf c p.1 p.2) (C.conjugateOf c q.1 q.2)
      (by simp [conjugateOf]) hpq
    have hh : C.second c.second+p.1 = C.second c.second+q.1 := by
      simpa only [C.conjugateOf_second_detect c hc] using h
    exact add_left_cancel hh
  have hv : p.2 = q.2 := by
    have hq : C.quotientMap tails (C.quadraticWord p.2*c*(C.quadraticWord p.2)⁻¹) =
        C.quotientMap tails (C.quadraticWord q.2*c*(C.quadraticWord q.2)⁻¹) := by
      have h := congrArg (fun x : C.Cut tails =>
        (C.quotientMap tails (C.baseWord q.1))⁻¹*x*C.quotientMap tails (C.baseWord q.1)) hpq
      simpa [conjugateOf,conjugator,hu,map_mul,map_inv,mul_assoc] using h
    have h := C.third_eq_of_quotient tails
      (C.quadraticWord p.2*c*(C.quadraticWord p.2)⁻¹) (C.quadraticWord q.2*c*(C.quadraticWord q.2)⁻¹)
      (by simp)
      (by rw [conjugate_of_first_zero _ _ (C.quadraticWord_first p.2),
        conjugate_of_first_zero _ _ (C.quadraticWord_first q.2)]) hq
    have hh : C.third c.third-p.2 = C.third c.third-q.2 := by
      simpa only [C.quadratic_conjugateOf_third_detect c hc] using h
    exact sub_right_inj.mp hh
  exact Prod.ext hu hv

theorem card_parameters : Nat.card ((Fin a → F) × (Fin b → F)) = 2^(a+b) := by
  rw [Nat.card_prod]
  simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  rw [pow_add]

theorem conjugator_mem_subgroup (tails : Fin m → V₃ n F) (H : Subgroup (C.Cut tails))
    (hgen : ∀ i, C.quotientMap tails (generator i) ∈ H) (u : Fin a → F) (v : Fin b → F) :
    C.quotientMap tails (C.conjugator u v) ∈ H := by
  let H' := H.comap (C.quotientMap tails)
  change C.conjugator u v ∈ H'
  apply H'.mul_mem
  · exact TruncatedMagnus.Certificate.word_mem_subgroup H' _ _ _ (fun i _ => hgen _)
  · apply TruncatedMagnus.Certificate.word_mem_subgroup H'
    intro i _
    exact H'.mul_mem (H'.mul_mem (H'.mul_mem (hgen _) (hgen _))
      (H'.inv_mem (hgen _))) (H'.inv_mem (hgen _))

/-- Every subgroup containing the generator images has at least `2^(a+b)`
conjugates of any element with elementary vector `cVec`. -/
theorem conjugacy_index_lower_subgroup_of_first (tails : Fin m → V₃ n F) (c : Group n F)
    (hc : c.first = C.cVec) (H : Subgroup (C.Cut tails)) (hcH : C.quotientMap tails c ∈ H)
    (hgen : ∀ i, C.quotientMap tails (generator i) ∈ H) :
    2^(a+b) ≤ (Subgroup.centralizer ({(⟨C.quotientMap tails c,hcH⟩ : H)} : Set H)).index := by
  rw [← card_parameters (a := a) (b := b)]
  let cH : H := ⟨C.quotientMap tails c,hcH⟩
  let g : (Fin a → F) × (Fin b → F) → H := fun p =>
    ⟨C.quotientMap tails (C.conjugator p.1 p.2),C.conjugator_mem_subgroup tails H hgen p.1 p.2⟩
  apply TruncatedMagnus.card_le_centralizer_index_of_conjugates_injective cH g
  intro p q hpq
  apply C.conjugateOf_injective tails c hc
  have h := congrArg (fun x : H => (x : C.Cut tails)) hpq
  simpa only [g,cH,Subgroup.coe_mul,Subgroup.coe_inv,conjugateOf,map_mul,map_inv] using h

end CutData
end UnitDistance.Sqrt241.Magnus
