module

public import UnitDistance.GroupAugmentationGenerators
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual filtered induction from a product basis

An actual basis whose vectors are `m_t` times local basis vectors gives
right-module coordinates. If its actual augmentation-power spans have the
additive weights, those coordinates identify the actual powers with shifted
local powers. The following Jennings modules construct all the basis inputs
from actual injective dimension-layer maps of finite 2-groups.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (R D P T J : Type*) [CommRing R] [Group D] [Group P]
variable (b : Module.Basis J R (A R D)) (β : Module.Basis (T × J) R (A R P))

/-- The ambient basis coefficients, curried and converted to actual local
group-algebra vectors. This is a genuine linear equivalence. -/
def productCoordinates : A R P ≃ₗ[R] (T →₀ A R D) :=
  β.repr.trans ((Finsupp.curryLinearEquiv R).trans (Finsupp.mapRange.linearEquiv b.repr.symm))

theorem productCoordinates_repr (a : A R P) (t : T) (j : J) :
    b.repr (productCoordinates R D P T J b β a t) j = β.repr a (t,j) := by
  change b.repr (b.repr.symm _) j = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem productCoordinates_basis (t : T) (j : J) :
    productCoordinates R D P T J b β (β (t,j)) = Finsupp.single t (b j) := by
  classical
  apply Finsupp.ext
  intro u
  apply b.repr.injective
  ext k
  rw [productCoordinates_repr]
  simp only [Module.Basis.repr_self,Finsupp.single_apply]
  by_cases hu : t = u
  · subst u
    simp [Finsupp.single_apply]
  · simp [hu]

variable [Fintype J] (f : D →* P) (m : T → A R P)
variable (hβ : ∀ t j, β (t,j) = m t * induced R D f (b j))

include hβ in
/-- Each whole local right-module summand is exactly one coordinate block. -/
theorem productCoordinates_block (t : T) (v : A R D) :
    productCoordinates R D P T J b β (m t * induced R D f v) = Finsupp.single t v := by
  classical
  have he : m t * induced R D f v = ∑ j, b.repr v j • β (t,j) := by
    simp_rw [hβ,← mul_smul_comm,← map_smul]
    rw [← Finset.mul_sum,← map_sum,b.sum_repr]
  rw [he,map_sum]
  simp only [map_smul,productCoordinates_basis]
  have hs := congrArg (Finsupp.lsingle t : A R D →ₗ[R] (T →₀ A R D)) (b.sum_repr v)
  simpa only [map_sum,map_smul,Finsupp.lsingle_apply] using hs

include hβ in
/-- The actual basis decomposition is right linear over the local algebra. -/
theorem productCoordinates_mul (a : A R P) (v : A R D) (t : T) :
    productCoordinates R D P T J b β (a * induced R D f v) t =
      productCoordinates R D P T J b β a t * v := by
  classical
  let lhs : A R P →ₗ[R] (T →₀ A R D) :=
    (productCoordinates R D P T J b β).toLinearMap.comp (rightMul R P (induced R D f v))
  let rhs : A R P →ₗ[R] (T →₀ A R D) :=
    (Finsupp.mapRange.linearMap (rightMul R D v)).comp
      (productCoordinates R D P T J b β).toLinearMap
  have he : lhs = rhs := by
    apply β.ext
    rintro ⟨u,j⟩
    change productCoordinates R D P T J b β (β (u,j) * induced R D f v) = _
    conv_lhs => rw [hβ,mul_assoc,← map_mul,productCoordinates_block R D P T J b β f m hβ]
    change Finsupp.single u (b j*v) =
      Finsupp.mapRange (rightMul R D v) (map_zero _) (productCoordinates R D P T J b β (β (u,j)))
    rw [productCoordinates_basis,Finsupp.mapRange_single]
    rfl
  exact congrArg (fun L : A R P →ₗ[R] (T →₀ A R D) => L a t) he

omit [Fintype J] in
/-- Membership in a weighted basis span is exactly vanishing of the
coefficients below that weight. -/
theorem mem_weighted_basis_span_iff (w : J → ℕ) (n : ℕ) (a : A R D) :
    a ∈ Submodule.span R {v | ∃ j, n ≤ w j ∧ v = b j} ↔
      ∀ j, w j < n → b.repr a j = 0 := by
  classical
  have he : {v | ∃ j, n ≤ w j ∧ v = b j} = b '' {j | n ≤ w j} := by
    ext v
    constructor
    · rintro ⟨j,hj,rfl⟩; exact ⟨j,hj,rfl⟩
    · rintro ⟨j,hj,rfl⟩; exact ⟨j,hj,rfl⟩
  rw [he,b.mem_span_image]
  constructor
  · intro h j hj
    by_contra hne
    have hw := h (Finsupp.mem_support_iff.mpr hne)
    change n ≤ w j at hw
    omega
  · intro h j hj
    have hne := Finsupp.mem_support_iff.mp hj
    change n ≤ w j
    by_contra hn
    exact hne (h j (by omega))

omit [Fintype J] in
/-- The exact actual filtration identity in the genuine module coordinates.
Natural subtraction means shifts at least `n` allow the entire local algebra. -/
theorem productCoordinates_mem_power_iff (u : T → ℕ) (v : J → ℕ)
    (hb : ∀ n, Submodule.span R {a | ∃ j, n ≤ v j ∧ a = b j} = power R D n)
    (hambient : ∀ n, Submodule.span R {a | ∃ p : T × J,
      n ≤ u p.1 + v p.2 ∧ a = β p} = power R P n) (a : A R P) (n : ℕ) :
    a ∈ power R P n ↔ ∀ t, productCoordinates R D P T J b β a t ∈ power R D (n-u t) := by
  rw [← hambient n,mem_weighted_basis_span_iff]
  simp_rw [← hb,mem_weighted_basis_span_iff,productCoordinates_repr]
  constructor
  · intro h t j hj
    exact h (t,j) (by dsimp only; omega)
  · intro h p hp
    exact h p.1 p.2 (by omega)

/-- Direct-sum local powers with independently specified nonnegative shifts. -/
def shiftedCoefficientPower (u : T → ℕ) (n : ℕ) : Submodule R (T →₀ A R D) where
  carrier := {c | ∀ t, c t ∈ power R D (n-u t)}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb t; exact Submodule.add_mem _ (ha t) (hb t)
  smul_mem' := by intro r a ha t; exact Submodule.smul_mem _ r (ha t)

omit [Fintype J] in
/-- The image of each actual ambient power is exactly the direct sum of
the shifted actual local powers, including surjectivity onto that subspace. -/
theorem map_power_productCoordinates (u : T → ℕ) (v : J → ℕ)
    (hb : ∀ n, Submodule.span R {a | ∃ j, n ≤ v j ∧ a = b j} = power R D n)
    (hambient : ∀ n, Submodule.span R {a | ∃ p : T × J,
      n ≤ u p.1+v p.2 ∧ a = β p} = power R P n) (n : ℕ) :
    (power R P n).map (productCoordinates R D P T J b β).toLinearMap =
      shiftedCoefficientPower R D T u n := by
  ext c
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (productCoordinates_mem_power_iff R D P T J b β u v hb hambient a n).mp ha
  · intro hc
    obtain ⟨a,rfl⟩ := (productCoordinates R D P T J b β).surjective c
    exact ⟨a,(productCoordinates_mem_power_iff R D P T J b β u v hb hambient a n).mpr hc,rfl⟩

end UnitDistance.GroupAugmentation
