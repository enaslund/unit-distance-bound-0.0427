module

public import UnitDistance.DyadicFinal

@[expose] public section
set_option backward.privateInPublic true


/-!
# Linear certificate soundness for the graded dyadic multiplication maps

A quotient remainder has exactly the specified subspace as its kernel. A
pivot certificate gives a lower bound on image dimension. Together with
rank-nullity and the already proved augmentation dimensions, this identifies
the simultaneous graded multiplication kernel without assuming its value.
-/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Dyadic.Graded
open Filtration

def remainder {r : ℕ} (b : Fin r → V) (p : Fin r → Fin 32) : V →ₗ[F] V where
  toFun v := v - ∑ j, v (p j) • b j
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]; abel
  map_smul' a v := by simp [smul_sub, Finset.smul_sum, smul_smul]

theorem remainder_eq_zero_iff {r : ℕ} (b : Fin r → V) (p : Fin r → Fin 32)
    (hp : ∀ i j, b i (p j) = if i = j then 1 else 0) (v : V) :
    remainder b p v = 0 ↔ v ∈ spanRows b := by
  constructor
  · intro h
    have he : v = ∑ j, v (p j) • b j := sub_eq_zero.mp h
    rw [he]
    exact sum_mem_spanRows b _
  · intro hv
    have hs : spanRows b ≤ (remainder b p).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change b i - ∑ j, b i (p j) • b j = 0
      simp [hp]
    exact hs hv

/-- A coordinate minor equal to the identity certifies independent images. -/
theorem independent_of_pivots {r : ℕ} {ι : Type*}
    (b : Fin r → ι → F) (p : Fin r → ι)
    (h : ∀ i j, b i (p j) = if i = j then 1 else 0) :
    LinearIndependent F b := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have hj := congrArg (fun v : ι → F => v (p j)) ha
  simpa [h] using hj

/-- Independent images inside a restricted range give the required rank bound. -/
theorem rank_lower_of_pivots {r : ℕ} {ι : Type*}
    (S : Submodule F V) (f : V →ₗ[F] (ι → F)) (w : Fin r → V)
    (hw : ∀ i, w i ∈ S) (p : Fin r → ι)
    (hp : ∀ i j, f (w i) (p j) = if i = j then 1 else 0) :
    r ≤ Module.finrank F (LinearMap.range (f.comp S.subtype)) := by
  let v : Fin r → LinearMap.range (f.comp S.subtype) :=
    fun i => ⟨f (w i), ⟨⟨w i, hw i⟩, rfl⟩⟩
  have hi : LinearIndependent F v :=
    LinearIndependent.of_comp (LinearMap.range (f.comp S.subtype)).subtype
      (independent_of_pivots (fun i => f (w i)) p hp)
  simpa using hi.fintype_card_le_finrank

/-- Rank-nullity turns the certified lower rank into the exact restricted
kernel, since the next filtration space is already known to be killed. -/
theorem kernel_eq_of_rank_lower {W : Type*} [AddCommGroup W] [Module F W]
    (S T : Submodule F V) (f : V →ₗ[F] W) (hTS : T ≤ S)
    (hTf : T ≤ f.ker) {r : ℕ}
    (hdim : Module.finrank F S = r + Module.finrank F T)
    (hrank : r ≤ Module.finrank F (LinearMap.range (f.comp S.subtype))) :
    ∀ v ∈ S, f v = 0 ↔ v ∈ T := by
  let T' := T.comap S.subtype
  let f' := f.comp S.subtype
  have hle : T' ≤ f'.ker := by
    intro v hv
    exact hTf hv
  have hT : Module.finrank F T' = Module.finrank F T :=
    (Submodule.comapSubtypeEquivOfLe hTS).finrank_eq
  have hk := f'.finrank_range_add_finrank_ker
  have hmono := Submodule.finrank_mono hle
  have he : T' = f'.ker := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    change Module.finrank F T' = Module.finrank F f'.ker
    change r ≤ Module.finrank F f'.range at hrank
    omega
  intro v hv
  have hm : (⟨v, hv⟩ : S) ∈ T' ↔ (⟨v, hv⟩ : S) ∈ f'.ker := by rw [he]
  exact hm.symm

end UnitDistance.Dyadic.Graded
