module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.ClosedKernelH2FiniteFamily
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Cohomology.RelativeNakayama
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Presentations.Profinite
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Recognizing a specified full family of pro-p relators

The relation bound and independent evaluations of invariant characters force
the specified relators to normally generate. The arithmetic construction of
the characters and the bound on actual H² remain separate obligations.
-/

open scoped Topology

namespace UnitDistance.SpecifiedRelators

open ProCGroups ProCGroups.ProC ProCGroups.Presentations
open ClassFieldTower.ProP ClassFieldTower.Cohomology

noncomputable section

private theorem independent_append_of_evaluations
    {k X : Type*} [Field k] {n : ℕ}
    (v : Fin n → X → k) (x : Fin n → X) (w : X → k)
    (heval : ∀ i j, v i (x j) = if i = j then 1 else 0)
    (hkill : ∀ j, w (x j) = 0) (hne : w ≠ 0) :
    LinearIndependent k (Fin.snoc v w) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hcoeff (j : Fin n) : a j.castSucc = 0 := by
    have he := congrFun ha (x j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hkill,
      mul_zero, add_zero, heval] at he
    simpa using he
  have hlast : a (Fin.last n) = 0 := by
    by_contra h
    apply hne
    funext y
    have he := congrFun ha y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hcoeff,
      zero_mul, Finset.sum_const_zero, zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left h
  exact Fin.lastCases hlast hcoeff i

/-- A specified family of `n` relators normally generates the actual closed
kernel if its invariant character evaluation matrix is the identity and the
quotient's degree-two continuous cohomology has dimension at most `n`. -/
theorem closedNormalClosure_eq_of_dual_characters
    {p : ℕ} [Fact p.Prime]
    {F : Type*} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (hF : HasPGroupOpenNormalBasis p F)
    (R : ClosedSubgroup F) [R.Normal]
    (hR : (R : Subgroup F) ≤ closedPowerCommutator p F)
    {n : ℕ} (ρ : Fin n → R)
    (χ : Fin n → R →ₜ* Multiplicative (ZMod p))
    (hχinv : ∀ (i : Fin n) (f : F) (r : R), χ i (MulAut.conjNormal f r) = χ i r)
    (heval : ∀ i j, (χ i (ρ j)).toAdd = if i = j then 1 else 0)
    [FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2)]
    (hbound : Module.finrank (ZMod p)
      (continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2) ≤ n) :
    closedNormalClosure (Set.range (fun i ↦ (ρ i : F))) = (R : Subgroup F) := by
  classical
  let K : ClosedSubgroup F :=
    { toSubgroup := closedNormalClosure (Set.range (fun i ↦ (ρ i : F)))
      isClosed' := closedNormalClosure_isClosed (Set.range (fun i ↦ (ρ i : F))) }
  let : K.Normal :=
    inferInstanceAs (closedNormalClosure (Set.range (fun i ↦ (ρ i : F)))).Normal
  have hKR : K ≤ R := by
    apply closedNormalClosure_le_closed_normal R.isClosed'
    rintro r ⟨i, rfl⟩
    exact (ρ i).2
  by_contra hneq
  have hstrict : K < R := lt_of_le_of_ne hKR (by
    intro h
    exact hneq (congrArg (fun L : ClosedSubgroup F ↦ (L : Subgroup F)) h))
  obtain ⟨ψ, hψne, hψkill, hψinv⟩ := relativeNakayama_character hF K R hstrict
  have hkill (j : Fin n) : (ψ (ρ j)).toAdd = 0 := by
    have hj : (ρ j : F) ∈ K :=
      subset_closedNormalClosure (Set.range (fun i ↦ (ρ i : F))) ⟨j, rfl⟩
    exact congrArg Multiplicative.toAdd (hψkill ⟨(ρ j : F), hj⟩)
  have hne : (fun r : R ↦ (ψ r).toAdd) ≠ 0 := by
    intro h
    apply hψne
    apply ContinuousMonoidHom.ext
    intro r
    exact Multiplicative.toAdd.injective (congrFun h r)
  let η : Fin (n + 1) → R →ₜ* Multiplicative (ZMod p) := Fin.snoc χ ψ
  have hηinv (i : Fin (n + 1)) (f : F) (r : R) :
      η i (MulAut.conjNormal f r) = η i r := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [η, Fin.snoc_last] using hψinv f r
    · simpa only [η, Fin.snoc_castSucc] using hχinv j f r
  have hηind : LinearIndependent (ZMod p) (fun i ↦ fun r : R ↦ (η i r).toAdd) := by
    have h := independent_append_of_evaluations
      (fun i r ↦ (χ i r).toAdd) ρ (fun r ↦ (ψ r).toAdd) heval hkill hne
    convert h using 1
    funext i r
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [η, Fin.snoc_last]
    · simp only [η, Fin.snoc_castSucc]
  have hb := invariant_character_family_card_le_finrank_h2 hF R hR η hηinv hηind
  have hbad : n + 1 ≤ n := by
    simpa only [Fintype.card_fin] using hb.trans hbound
  exact Nat.not_succ_le_self n hbad

end

end UnitDistance.SpecifiedRelators
