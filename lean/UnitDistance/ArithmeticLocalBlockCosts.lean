module

public import UnitDistance.OddLocalHilbert
public import UnitDistance.CyclicLocalHilbert
public import UnitDistance.FilteredOptimizedGolodShafarevich

@[expose] public section
set_option backward.privateInPublic true


/-! The eleven nondyadic local blocks, their actual groups and generators,
and the exact scalar specialization of their proved Hilbert costs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace UnitDistance.ArithmeticLocalBlocks
open GroupAugmentation Polynomial

abbrev Index := Option (Fin 5 ⊕ Fin 5)
def GeneratorType : Index → Type
  | none => Fin 1
  | some (.inl _) => Fin 2
  | some (.inr _) => Fin 1
def LocalGroup : Index → Type
  | none => OddLocal.Cyclic 2
  | some (.inl i) => OddLocal.D i
  | some (.inr _) => OddLocal.Cyclic 4

instance generatorFintype (j : Index) : Fintype (GeneratorType j) := by
  cases j with
  | none => exact inferInstanceAs (Fintype (Fin 1))
  | some j => cases j <;> dsimp [GeneratorType] <;> infer_instance
instance localGroup (j : Index) : Group (LocalGroup j) := by
  cases j with
  | none => exact inferInstanceAs (Group (OddLocal.Cyclic 2))
  | some j => cases j <;> dsimp [LocalGroup] <;> infer_instance
instance localFinite (j : Index) : Finite (LocalGroup j) := by
  cases j with
  | none => exact inferInstanceAs (Finite (OddLocal.Cyclic 2))
  | some j => cases j <;> dsimp [LocalGroup] <;> infer_instance

def generators : ∀ j : Index,GeneratorType j → LocalGroup j
  | none => fun _ => OddLocal.cyclicGenerator 2
  | some (.inl i) => ![OddLocal.inertia i,OddLocal.frobenius i]
  | some (.inr _) => fun _ => OddLocal.cyclicGenerator 4

theorem isTwoGroup (j : Index) : IsPGroup 2 (LocalGroup j) := by
  cases j with
  | none => exact RetainedCyclic.cyclicTwo_isTwoGroup
  | some j =>
    cases j with
    | inl i => exact OddLocal.isTwoGroup i
    | inr _ => exact RetainedCyclic.cyclicFour_isTwoGroup

theorem generates (j : Index) : Subgroup.closure (Set.range (generators j))=⊤ := by
  cases j with
  | none =>
    change Subgroup.closure (Set.range (fun _ : Fin 1 => OddLocal.cyclicGenerator 2))=⊤
    simpa using RetainedCyclic.cyclic_generates 2
  | some j =>
    cases j with
    | inl i =>
      have hr : Set.range (generators (some (.inl i)))=({OddLocal.inertia i,OddLocal.frobenius i} : Set (OddLocal.D i)) := by
        ext x
        change (∃ y : Fin 2,![OddLocal.inertia i,OddLocal.frobenius i] y=x) ↔ _
        simp [Fin.exists_fin_two,eq_comm]
      rw [hr]
      exact OddLocal.generators i
    | inr i =>
      change Subgroup.closure (Set.range (fun _ : Fin 1 => OddLocal.cyclicGenerator 4))=⊤
      simpa using RetainedCyclic.cyclic_generates 4

def cost (j : Index) (t : ℝ) : ℝ :=
  (Fintype.card (GeneratorType j) : ℝ)*t-1+
    1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (LocalGroup j))

theorem cost_infinity (t : ℝ) : cost none t=t-1+1/(1+t) := by
  change (Fintype.card (Fin 1) : ℝ)*t-1+1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (OddLocal.Cyclic 2))=_
  rw [Fintype.card_fin,RetainedCyclic.cyclicTwo_hilbert]
  norm_num [Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_X]

theorem cost_odd (i : Fin 5) (t : ℝ) : cost (some (.inl i)) t=
    2*t-1+1/((1+t)^2*(if i.val<2 then 1 else 1+t^2)) := by
  change 2*t-1+1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (OddLocal.D i))=_
  rw [OddLocal.hilbertPolynomial_eq]
  split_ifs <;> simp only [Polynomial.eval₂_mul,Polynomial.eval₂_pow,
    Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_X,mul_one]

theorem cost_extra (i : Fin 5) (t : ℝ) : cost (some (.inr i)) t=
    t-1+1/((1+t)*(1+t^2)) := by
  change (Fintype.card (Fin 1) : ℝ)*t-1+1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (OddLocal.Cyclic 4))=_
  rw [Fintype.card_fin,RetainedCyclic.cyclicFour_hilbert]
  norm_num [Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_add,
    Polynomial.eval₂_one,Polynomial.eval₂_X]

theorem sum_cost (t : ℝ) (ht : 0≤t) :
    (∑ j : Index,cost j t)=
      2*(2*t-1+1/(1+t)^2)+3*(2*t-1+1/((1+t)^2*(1+t^2)))+
        t^2/(1+t)+5*t^4/((1+t)*(1+t^2)) := by
  rw [Fintype.sum_option,Fintype.sum_sum_type]
  simp only [cost_infinity,cost_odd,cost_extra,Fin.sum_univ_succ]
  norm_num only [Fin.val_zero,Fin.val_succ,ite_true,ite_false,Nat.reduceAdd,Nat.reduceLT,
    mul_one,Finset.sum_empty,add_zero]
  have h1 : 1+t≠0 := by positivity
  have h2 : 1+t^2≠0 := by positivity
  field_simp
  <;> ring

theorem optimized_coefficient (t : ℚ) (ht : 0≤t) :
    1-7*(t : ℝ)+(∑ j : Index,cost j t)+(3*(t : ℝ)-1+1/((1+t)^3*(1+t^2)^2))-
      (t : ℝ)^2*(1-t^7/((1+t)^3*(1+t^2)^2))=(optimizedTowerPolynomial t : ℝ) := by
  rw [sum_cost t (by exact_mod_cast ht)]
  unfold optimizedTowerPolynomial
  push_cast
  ring

theorem optimized_coefficient_negative :
    1-7*((11 : ℝ)/34)+(∑ j : Index,cost j ((11 : ℝ)/34))+
      (3*((11 : ℝ)/34)-1+1/((1+(11 : ℝ)/34)^3*(1+((11 : ℝ)/34)^2)^2))-
      ((11 : ℝ)/34)^2*(1-((11 : ℝ)/34)^7/
        ((1+(11 : ℝ)/34)^3*(1+((11 : ℝ)/34)^2)^2))<0 := by
  have h := optimized_coefficient (11/34) (by norm_num)
  have hn : (optimizedTowerPolynomial (11/34) : ℝ)<0 := by
    exact_mod_cast optimizedTowerPolynomial_negative
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h.trans_lt hn

end UnitDistance.ArithmeticLocalBlocks
