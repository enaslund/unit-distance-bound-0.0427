module

public import UnitDistance.KummerInvariantRadicand

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual norm-extension catalog

The seventeen integer rows are independently defined from the manuscript.
Their norm identities are kernel-checked. For actual square roots in an
actual field, the associated radicands and semilinear lift multipliers obey
the corresponding field identities and twisted-norm signs.
-/

noncomputable section
namespace UnitDistance.NormExtensionCatalog

structure Row where
  A : ℤ
  B : ℤ
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq

/-- The exact seventeen raw norm-extension rows. -/
def catalog : Fin 17 → Row :=
  ![⟨-1,65,4,7,1⟩,⟨-55,91,6,1,1⟩,⟨-2,33,1,4,1⟩,
    ⟨-55,14,1,1,2⟩,⟨-55,26,7,1,2⟩,⟨-7,2,1,1,2⟩,
    ⟨-10,1001,1,10,1⟩,⟨22,273,19,2,1⟩,⟨-39,55,4,1,1⟩,
    ⟨-35,429,1,7,2⟩,⟨-143,42,5,1,2⟩,⟨-3,13,1,2,1⟩,
    ⟨-26,105,1,2,1⟩,⟨-6,385,1,8,1⟩,⟨-14,65,3,2,1⟩,
    ⟨-11,5,3,1,2⟩,⟨-1,13,-2,3,1⟩]

/-- Every catalog row satisfies its exact integer norm identity. -/
theorem catalog_norm (i : Fin 17) :
    (catalog i).x^2-(catalog i).A*(catalog i).y^2 = (catalog i).B*(catalog i).z^2 := by
  have h : ∀ i : Fin 17,
      (catalog i).x^2-(catalog i).A*(catalog i).y^2 = (catalog i).B*(catalog i).z^2 := by
    decide +kernel
  exact h i

/-- All right-hand norm values are nonzero. -/
theorem catalog_nonzero (i : Fin 17) : (catalog i).B ≠ 0 ∧ (catalog i).z ≠ 0 := by
  have h : ∀ i : Fin 17, (catalog i).B ≠ 0 ∧ (catalog i).z ≠ 0 := by decide +kernel
  exact h i

variable {E : Type*} [Field E] [CharZero E]

/-- The actual algebraic radicand `x+y√A`. -/
def alpha (i : Fin 17) (a : E) : E := (catalog i).x + (catalog i).y*a

/-- The checked integer identity holds in every actual characteristic-zero
field containing the indicated square root. -/
theorem alpha_norm (i : Fin 17) (a : E) (ha : a^2 = (catalog i).A) :
    alpha i a * alpha i (-a) = (catalog i).B*((catalog i).z : E)^2 := by
  have hn : ((catalog i).x : E)^2-((catalog i).A : E)*(catalog i).y^2 =
      (catalog i).B*((catalog i).z : E)^2 := by exact_mod_cast catalog_norm i
  calc
    alpha i a * alpha i (-a) = ((catalog i).x : E)^2-((catalog i).y : E)^2*a^2 := by
      unfold alpha
      ring
    _ = ((catalog i).x : E)^2-((catalog i).A : E)*(catalog i).y^2 := by rw [ha]; ring
    _ = _ := hn

/-- The actual catalog radicands are nonzero. -/
theorem alpha_ne_zero (i : Fin 17) (a : E) (ha : a^2 = (catalog i).A) :
    alpha i a ≠ 0 := by
  have hB : ((catalog i).B : E) ≠ 0 := by exact_mod_cast (catalog_nonzero i).1
  have hz : ((catalog i).z : E) ≠ 0 := by exact_mod_cast (catalog_nonzero i).2
  have hn := alpha_norm i a ha
  intro h
  rw [h,zero_mul] at hn
  exact (mul_ne_zero hB (pow_ne_zero 2 hz)) hn.symm

/-- The sign attached to the actual action on one square root. -/
def sign (b : Bool) : E := if b then -1 else 1

variable (σ : Gal(E/ℚ))

/-- Action on the actual radicand is determined by action on its actual root. -/
theorem map_alpha (i : Fin 17) (a : E) (ε : Bool)
    (hσa : σ a = sign ε*a) :
    σ (alpha i a) = if ε then alpha i (-a) else alpha i a := by
  cases ε
  · have hh : σ a = a := by simpa [sign] using hσa
    simp [alpha,hh]
  · have hh : σ a = -a := by simpa [sign] using hσa
    simp [alpha,hh]

/-- The manuscript's explicit multiplier for lifting an actual base automorphism. -/
def multiplier (i : Fin 17) (a b : E) (ε : Bool) : E :=
  if ε then (catalog i).z*b/alpha i a else 1

/-- The actual norm identity supplies the invariant-squareclass equation. -/
theorem multiplier_twist (i : Fin 17) (a b : E)
    (ha : a^2 = (catalog i).A) (hb : b^2 = (catalog i).B)
    (ε : Bool) (hσa : σ a = sign ε*a) :
    alpha i a * (multiplier i a b ε)^2 = σ (alpha i a) := by
  rw [map_alpha σ i a ε hσa]
  cases ε
  · simp [multiplier]
  · change alpha i a * ((catalog i).z*b/alpha i a)^2 = alpha i (-a)
    have hα := alpha_ne_zero i a ha
    calc
      alpha i a * ((catalog i).z*b/alpha i a)^2 =
          ((catalog i).B*((catalog i).z : E)^2)/alpha i a := by
        rw [div_pow,mul_pow,hb]
        field_simp
      _ = alpha i (-a) := (div_eq_iff hα).mpr (by
        simpa [mul_comm] using (alpha_norm i a ha).symm)

/-- The twisted norm of the actual lift multiplier is the product of the
two actual square-root signs. -/
theorem multiplier_twisted_norm (i : Fin 17) (a b : E)
    (ha : a^2 = (catalog i).A) (hb : b^2 = (catalog i).B)
    (ε δ : Bool) (hσa : σ a = sign ε*a) (hσb : σ b = sign δ*b) :
    multiplier i a b ε * σ (multiplier i a b ε) = sign (ε && δ) := by
  cases ε
  · simp [multiplier,sign]
  · change (catalog i).z*b/alpha i a * σ ((catalog i).z*b/alpha i a) = sign δ
    rw [map_div₀,map_mul,map_intCast,map_alpha σ i a true hσa,hσb]
    change (catalog i).z*b/alpha i a * ((catalog i).z*(sign δ*b)/alpha i (-a)) = sign δ
    have hα := alpha_ne_zero i a ha
    have hα' := alpha_ne_zero i (-a) (by simpa using ha)
    have hn := alpha_norm i a ha
    cases δ <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
    · field_simp
      linear_combination -hn + ((catalog i).z : E)^2*hb
    · field_simp
      linear_combination hn - ((catalog i).z : E)^2*hb

end UnitDistance.NormExtensionCatalog

namespace UnitDistance.NormExtensionCatalog
open scoped BigOperators
variable {E : Type*} [Field E] [CharZero E]

/-- An actual product of the independently defined catalog radicands. -/
def radicand (s : Finset (Fin 17)) (a : Fin 17 → E) : E := ∏ i ∈ s, alpha i (a i)

/-- The actual product multiplier corresponding to a catalog word. -/
def productMultiplier (s : Finset (Fin 17)) (a b : Fin 17 → E)
    (ε : Fin 17 → Bool) : E := ∏ i ∈ s, multiplier i (a i) (b i) (ε i)

/-- Products of catalog radicands are nonzero. -/
theorem radicand_ne_zero (s : Finset (Fin 17)) (a : Fin 17 → E)
    (ha : ∀ i ∈ s, (a i)^2 = (catalog i).A) : radicand s a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact alpha_ne_zero i (a i) (ha i hi)

variable (σ : Gal(E/ℚ))

/-- Product radicands satisfy the actual invariant-squareclass identity. -/
theorem productMultiplier_twist (s : Finset (Fin 17)) (a b : Fin 17 → E)
    (ha : ∀ i ∈ s, (a i)^2 = (catalog i).A)
    (hb : ∀ i ∈ s, (b i)^2 = (catalog i).B)
    (ε : Fin 17 → Bool) (hσa : ∀ i ∈ s, σ (a i) = sign (ε i)*a i) :
    radicand s a * (productMultiplier s a b ε)^2 = σ (radicand s a) := by
  unfold radicand productMultiplier
  rw [map_prod,← Finset.prod_pow,← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi =>
    multiplier_twist σ i (a i) (b i) (ha i hi) (hb i hi) (ε i) (hσa i hi)

/-- The actual product lift has the product of the computed signs. -/
theorem productMultiplier_twisted_norm (s : Finset (Fin 17)) (a b : Fin 17 → E)
    (ha : ∀ i ∈ s, (a i)^2 = (catalog i).A)
    (hb : ∀ i ∈ s, (b i)^2 = (catalog i).B)
    (ε δ : Fin 17 → Bool) (hσa : ∀ i ∈ s, σ (a i) = sign (ε i)*a i)
    (hσb : ∀ i ∈ s, σ (b i) = sign (δ i)*b i) :
    productMultiplier s a b ε * σ (productMultiplier s a b ε) =
      ∏ i ∈ s, sign (ε i && δ i) := by
  unfold productMultiplier
  rw [map_prod,← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi =>
    multiplier_twisted_norm σ i (a i) (b i) (ha i hi) (hb i hi) (ε i) (δ i)
      (hσa i hi) (hσb i hi)

/-- A computed nontrivial product sign under an actual involution proves
that the actual product radicand is nonsquare. -/
theorem radicand_nonsquare_of_sign
    (hσ : Function.Involutive σ) (s : Finset (Fin 17)) (a b : Fin 17 → E)
    (ha : ∀ i ∈ s, (a i)^2 = (catalog i).A)
    (hb : ∀ i ∈ s, (b i)^2 = (catalog i).B)
    (ε δ : Fin 17 → Bool) (hσa : ∀ i ∈ s, σ (a i) = sign (ε i)*a i)
    (hσb : ∀ i ∈ s, σ (b i) = sign (δ i)*b i)
    (hsign : (∏ i ∈ s, sign (ε i && δ i) : E) ≠ 1) :
    KummerInvariant.Nonsquare (radicand s a) := by
  apply KummerInvariant.nonsquare_of_twisted_norm σ hσ (radicand s a)
    (productMultiplier s a b ε) (radicand_ne_zero s a ha)
    (productMultiplier_twist σ s a b ha hb ε hσa)
  rwa [productMultiplier_twisted_norm σ s a b ha hb ε δ hσa hσb]

/-- Every actual automorphism acts on a square root of an integer by a sign. -/
theorem exists_root_sign (a : E) (A : ℤ) (ha : a^2 = A) :
    ∃ ε : Bool, σ a = sign ε*a := by
  have hs : (σ a)^2 = a^2 := by rw [← map_pow,ha,map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact ⟨false,by simpa [sign] using h⟩
  · exact ⟨true,by simpa [sign] using h⟩

/-- Actual catalog product radicands have invariant squareclasses under
all automorphisms of the actual base field. -/
theorem radicand_invariant (s : Finset (Fin 17)) (a b : Fin 17 → E)
    (ha : ∀ i, (a i)^2 = (catalog i).A) (hb : ∀ i, (b i)^2 = (catalog i).B) :
    ∃ u : E, radicand s a*u^2 = σ (radicand s a) := by
  choose ε hε using fun i => exists_root_sign σ (a i) (catalog i).A (ha i)
  exact ⟨productMultiplier s a b ε,
    productMultiplier_twist σ s a b (fun i _ => ha i) (fun i _ => hb i) ε (fun i _ => hε i)⟩

end UnitDistance.NormExtensionCatalog
