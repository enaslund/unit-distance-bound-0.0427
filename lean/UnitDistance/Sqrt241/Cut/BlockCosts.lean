module

public import UnitDistance.Sqrt241.Cut.LocalFamily
public import UnitDistance.Sqrt241.TowerPolynomial

@[expose] public section
set_option backward.privateInPublic true


/-!
# Block costs over `ℚ(√241)` and the polynomial `P_B`

The ten blocks other than the distinguished dyadic place `𝔭₁` have the
costs `c₁ = t²/(1+t)` (two real places), `c₂ = 2t - 1 + 1/(1+t)²` (four tame
places), `d_D = 3t - 1 + 1/((1+t)³(1+t²)²)` (the ordinary dyadic block `𝔭₂`)
and `c₄ = t⁴/((1+t)(1+t²))` (three caps), computed from the proved Hilbert
polynomials of the local groups. With the distinguished dyadic cost and saving,
the optimized coefficient with eight generators is exactly
`Sqrt241.towerPolynomial t`, negative at `t = 34/117`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace UnitDistance.Sqrt241.Cut
open GroupAugmentation Polynomial OddLocal

def cost (j : Index) (t : ℝ) : ℝ :=
  (Fintype.card (GeneratorType j) : ℝ)*t-1+
    1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (LocalGroup j))

theorem cost_real (i : Fin 2) (t : ℝ) : cost (.inl i) t = t-1+1/(1+t) := by
  change (Fintype.card (Fin 1) : ℝ)*t-1+
    1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (Cyclic 2)) = _
  rw [Fintype.card_fin,RetainedCyclic.cyclicTwo_hilbert]
  norm_num [Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_X]

theorem cost_tame (q : Fin 4) (t : ℝ) : cost (.inr (.inl q)) t = 2*t-1+1/(1+t)^2 := by
  change (Fintype.card (Fin 2) : ℝ)*t-1+
    1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (OddLocal.D 0)) = _
  rw [Fintype.card_fin,OddLocal.hilbertPolynomial_eq]
  simp only [Fin.val_zero,Nat.ofNat_pos,ite_true,mul_one,Polynomial.eval₂_pow,
    Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_X]
  norm_num

theorem cost_dyadic (u : Unit) (t : ℝ) :
    cost (.inr (.inr (.inl u))) t = 3*t-1+1/((1+t)^3*(1+t^2)^2) := by
  change (Fintype.card (Fin 3) : ℝ)*t-1+
    1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial Dyadic.D) = _
  rw [Fintype.card_fin,dyadic_hilbertPolynomial_eq]
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_add,
    Polynomial.eval₂_one,Polynomial.eval₂_X]
  norm_num

theorem cost_cap (k : Fin 3) (t : ℝ) :
    cost (.inr (.inr (.inr k))) t = t-1+1/((1+t)*(1+t^2)) := by
  change (Fintype.card (Fin 1) : ℝ)*t-1+
    1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (Cyclic 4)) = _
  rw [Fintype.card_fin,RetainedCyclic.cyclicFour_hilbert]
  norm_num [Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_add,
    Polynomial.eval₂_one,Polynomial.eval₂_X]

theorem sum_cost (t : ℝ) (ht : 0 ≤ t) :
    (∑ j : Index, cost j t) =
      2*(t^2/(1+t))+4*(2*t-1+1/(1+t)^2)+(3*t-1+1/((1+t)^3*(1+t^2)^2))+
        3*(t^4/((1+t)*(1+t^2))) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [cost_real,cost_tame,cost_dyadic,cost_cap,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,Fintype.card_unit,nsmul_eq_mul]
  have h1 : 1+t ≠ 0 := by positivity
  have h2 : 1+t^2 ≠ 0 := by positivity
  field_simp
  ring

/-- The optimized coefficient with eight generators and the `B` blocks is `P_B`. -/
theorem optimized_coefficient (t : ℚ) (ht : 0 ≤ t) :
    1-(8 : ℝ)*t+(∑ j : Index, cost j t)+(3*(t : ℝ)-1+1/((1+t)^3*(1+t^2)^2))-
      (t : ℝ)^2*(1-t^7/((1+t)^3*(1+t^2)^2)) = (Sqrt241.towerPolynomial t : ℝ) := by
  rw [sum_cost t (by exact_mod_cast ht)]
  unfold Sqrt241.towerPolynomial
  push_cast
  ring

theorem optimized_coefficient_negative :
    1-(8 : ℝ)*((34 : ℝ)/117)+(∑ j : Index, cost j ((34 : ℝ)/117))+
      (3*((34 : ℝ)/117)-1+1/((1+(34 : ℝ)/117)^3*(1+((34 : ℝ)/117)^2)^2))-
      ((34 : ℝ)/117)^2*(1-((34 : ℝ)/117)^7/
        ((1+(34 : ℝ)/117)^3*(1+((34 : ℝ)/117)^2)^2)) < 0 := by
  have h := optimized_coefficient (34/117) (by norm_num)
  have hn : (Sqrt241.towerPolynomial (34/117) : ℝ) < 0 := by
    exact_mod_cast Sqrt241.towerPolynomial_negative
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h.trans_lt hn

end UnitDistance.Sqrt241.Cut
