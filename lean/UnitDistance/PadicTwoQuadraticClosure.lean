module

public import UnitDistance.PadicTwoSquareclasses
public import Mathlib.FieldTheory.KummerExtension

@[expose] public section
set_option backward.privateInPublic true


/-! Quadratic extensions of Q₂ lie in any field with the three displayed
roots of −1, 2, and 5. The generic quadratic-generator argument is adapted
from Naganori Yamaguchi, SawinTotallyRealTowers/QuadraticGenerator.lean at
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0). -/
noncomputable section
namespace UnitDistance.QuadraticRadical

/-- Every characteristic-zero quadratic extension has an actual nonsquare radical generator. -/
theorem exists_generator (F K : Type*) [Field F] [CharZero F] [Field K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K] :
    ∃ (d : F) (r : K),r^2=algebraMap F K d ∧
      IntermediateField.adjoin F ({r} : Set K)=⊤ ∧ ¬ IsSquare d ∧ d≠0 := by
  have hroots : (primitiveRoots (Module.finrank F K) F).Nonempty := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F K]
    refine ⟨-1,(mem_primitiveRoots (by decide : 0<2)).mpr ?_⟩
    exact IsPrimitiveRoot.neg_one 0 (by decide)
  obtain ⟨r,⟨d,hd⟩,hr⟩ := exists_root_adjoin_eq_top_of_isCyclic F K hroots
  have hsq : r^2=algebraMap F K d := by
    simpa only [Algebra.IsQuadraticExtension.finrank_eq_two F K] using hd.symm
  have hi : Irreducible (Polynomial.X^2-Polynomial.C d) := by
    simpa only [Algebra.IsQuadraticExtension.finrank_eq_two F K] using
      irreducible_X_pow_sub_C_of_root_adjoin_eq_top hd.symm hr
  refine ⟨d,r,hsq,hr,?_,?_⟩
  · intro h
    obtain ⟨a,ha⟩ := h.exists_sq
    exact (pow_ne_of_irreducible_X_pow_sub_C hi (dvd_refl 2) (by decide) a) ha.symm
  · exact ne_zero_of_irreducible_X_pow_sub_C' (by decide : (2 : ℕ)≠1) hi

end UnitDistance.QuadraticRadical
namespace UnitDistance.PadicTwo
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable (K : Type*) [Field K] [Algebra ℚ_[2] K]

/-- A field with square roots of −1, 2 and 5 contains square roots of every base element. -/
theorem every_base_element_isSquare (a b c : K)
    (ha : a^2=-1) (hb : b^2=2) (hc : c^2=5) (d : ℚ_[2]) :
    IsSquare (algebraMap ℚ_[2] K d) := by
  by_cases hd : d=0
  · simp [hd]
  obtain ⟨i,e,z,hz⟩ := squareclass d hd
  have hi : IsSquare (unitRepresentative i : K) := by
    fin_cases i
    · norm_num [unitRepresentative]
    · exact ⟨a,by simpa [unitRepresentative,pow_two] using ha.symm⟩
    · exact ⟨c,by simpa [unitRepresentative,pow_two] using hc.symm⟩
    · refine ⟨a*c,?_⟩
      have h : (a*c)^2= -5 := by rw [mul_pow,ha,hc]; ring
      simpa [unitRepresentative,pow_two] using h.symm
  have he : IsSquare ((2 : K)^e.val) := by
    fin_cases e
    · simp
    · exact ⟨b,by simpa [pow_two] using hb.symm⟩
  rw [hz,map_mul,map_pow]
  have hrep : algebraMap ℚ_[2] K (representative i e : ℚ_[2])=
      (unitRepresentative i : K)*(2 : K)^e.val := by
    rw [map_intCast]
    simp only [representative,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  rw [hrep]
  exact (hi.mul he).mul (IsSquare.sq _)

/-- Every root of a base element belongs to an intermediate field containing the three roots. -/
theorem root_mem (E : IntermediateField ℚ_[2] K)
    (a b c : E) (ha : a^2=-1) (hb : b^2=2) (hc : c^2=5)
    (d : ℚ_[2]) (r : K) (hr : r^2=algebraMap ℚ_[2] K d) : r∈E := by
  obtain ⟨s,hs⟩ := every_base_element_isSquare E a b c ha hb hc d
  have hs' : (s : K)^2=algebraMap ℚ_[2] K d := by
    have h := congrArg (fun x : E => (x : K)) hs
    simpa [pow_two] using h.symm
  have he : r=(s : K) ∨ r= -(s : K) := by
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp (hr.trans hs'.symm)
  rcases he with he | he
  · exact he ▸ s.property
  · rw [he]
    exact E.neg_mem s.property

/-- Any actual quadratic intermediate field is contained in the displayed multiquadratic field. -/
theorem quadratic_le (E L : IntermediateField ℚ_[2] K)
    (a b c : E) (ha : a^2=-1) (hb : b^2=2) (hc : c^2=5)
    (hL : Module.finrank ℚ_[2] L=2) : L≤E := by
  letI : Algebra.IsQuadraticExtension ℚ_[2] L := ⟨hL⟩
  obtain ⟨d,r,hr,hgen,_⟩ := QuadraticRadical.exists_generator ℚ_[2] L
  have hmem : (r : K)∈E := root_mem K E a b c ha hb hc d r (by
    exact congrArg (fun x : L => (x : K)) hr)
  have hle : IntermediateField.adjoin ℚ_[2] ({r} : Set L)≤E.comap L.val := by
    exact IntermediateField.adjoin_simple_le_iff.mpr hmem
  rw [hgen] at hle
  intro x hx
  exact hle (show (⟨x,hx⟩ : L)∈(⊤ : IntermediateField ℚ_[2] L) from trivial)

end UnitDistance.PadicTwo
