module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.NoncommRing

@[expose] public section
set_option backward.privateInPublic true


/-!
# Functorial augmentation powers and actual dimension subgroups

All powers are spans of products in the ordinary, possibly noncommutative,
group algebra. No presentation, rank certificate, or desired Hilbert value
enters their definitions. This provides the group-theoretic filtration
interface needed before applying a filtered induction theorem.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]

abbrev A := MonoidAlgebra R G

def delta {G : Type*} [Group G] (g : G) : A R G := MonoidAlgebra.single g 1

@[simp] theorem delta_one : delta R (1 : G) = 1 := rfl
@[simp] theorem delta_mul (g h : G) : delta R g * delta R h = delta R (g * h) := by
  simp [delta, MonoidAlgebra.single_mul_single]

/-- The ordinary augmentation, sending every group basis element to one. -/
def augmentation : A R G →ₐ[R] R := MonoidAlgebra.lift R R G 1

@[simp] theorem augmentation_single (g : G) (r : R) :
    augmentation R G (MonoidAlgebra.single g r) = r := by
  simp [augmentation, MonoidAlgebra.lift_single]

@[simp] theorem augmentation_delta (g : G) : augmentation R G (delta R g) = 1 := by
  simp [delta]

/-- Ordinary powers of the augmentation ideal, expressed without a
commutative-ideal API. -/
def power : ℕ → Submodule R (A R G)
  | 0 => ⊤
  | n + 1 => Submodule.span R {v | ∃ a ∈ power n,
      ∃ b : A R G, augmentation R G b = 0 ∧ v = a * b}

@[simp] theorem power_zero : power R G 0 = ⊤ := rfl

theorem power_one : power R G 1 = (augmentation R G).toLinearMap.ker := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨a, _, b, hb, rfl⟩
    change augmentation R G (a * b) = 0
    simp [hb]
  · intro v hv
    exact Submodule.subset_span ⟨1, by trivial, v, hv, (one_mul v).symm⟩

theorem mul_mem_succ {n : ℕ} {a b : A R G}
    (ha : a ∈ power R G n) (hb : augmentation R G b = 0) :
    a * b ∈ power R G (n + 1) :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

/-- Every power is a right ideal of the actual group algebra. -/
theorem mul_mem_right (n : ℕ) (a b : A R G) (ha : a ∈ power R G n) :
    a * b ∈ power R G n := by
  cases n with
  | zero => trivial
  | succ n =>
    induction ha using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hv
      rw [mul_assoc]
      exact mul_mem_succ R G hx (by simp [hy])
    | zero => simp
    | add x y _ _ hx hy => simpa [add_mul] using (power R G (n+1)).add_mem hx hy
    | smul r x _ hx => simpa [smul_mul_assoc] using (power R G (n+1)).smul_mem r hx

/-- Every power is also a left ideal; no commutativity of the group is used. -/
theorem mul_mem_left (n : ℕ) (a b : A R G) (hb : b ∈ power R G n) :
    a * b ∈ power R G n := by
  induction n generalizing b with
  | zero => trivial
  | succ n ih =>
    induction hb using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hv
      rw [← mul_assoc]
      exact mul_mem_succ R G (ih _ hx) hy
    | zero => simp
    | add x y _ _ hx hy => simpa [mul_add] using (power R G (n+1)).add_mem hx hy
    | smul r x _ hx => simpa [mul_smul_comm] using (power R G (n+1)).smul_mem r hx

theorem power_succ_le (n : ℕ) : power R G (n + 1) ≤ power R G n := by
  apply Submodule.span_le.mpr
  rintro v ⟨a, ha, b, _, rfl⟩
  exact mul_mem_right R G n a b ha

theorem power_antitone : Antitone (power R G) :=
  antitone_nat_of_succ_le (power_succ_le R G)

/-- Multiplication respects the sum of the actual augmentation degrees. -/
theorem mul_mem_add {m n : ℕ} {a b : A R G}
    (ha : a ∈ power R G m) (hb : b ∈ power R G n) :
    a * b ∈ power R G (m + n) := by
  induction n generalizing b with
  | zero => simpa using mul_mem_right R G m a b ha
  | succ n ih =>
    induction hb using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hv
      rw [← mul_assoc]
      exact mul_mem_succ R G (ih hx) hy
    | zero => simp
    | add x y _ _ hx hy => simpa [mul_add] using (power R G (m+(n+1))).add_mem hx hy
    | smul r x _ hx => simpa [mul_smul_comm] using (power R G (m+(n+1))).smul_mem r hx

/-- Dimension subgroups defined by these actual augmentation powers. -/
def dimensionSubgroup (n : ℕ) : Subgroup G where
  carrier := {g | delta R g - 1 ∈ power R G n}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    have hm := mul_mem_right R G n (delta R g - 1) (delta R h) hg
    have he : delta R (g*h) - 1 = (delta R g - 1) * delta R h + (delta R h - 1) := by
      rw [← delta_mul]
      noncomm_ring
    change delta R (g*h) - 1 ∈ power R G n
    rw [he]
    exact (power R G n).add_mem hm hh
  inv_mem' {g} hg := by
    have hm := mul_mem_right R G n (delta R g - 1) (delta R g⁻¹) hg
    have he : delta R g⁻¹ - 1 = -((delta R g - 1) * delta R g⁻¹) := by
      simp [sub_mul]
    change delta R g⁻¹ - 1 ∈ power R G n
    rw [he]
    exact (power R G n).neg_mem hm

@[simp] theorem mem_dimensionSubgroup (n : ℕ) (g : G) :
    g ∈ dimensionSubgroup R G n ↔ delta R g - 1 ∈ power R G n := Iff.rfl

@[simp] theorem dimensionSubgroup_zero : dimensionSubgroup R G 0 = ⊤ := by
  ext; simp

@[simp] theorem dimensionSubgroup_one : dimensionSubgroup R G 1 = ⊤ := by
  ext g
  simp [power_one]

theorem dimensionSubgroup_antitone : Antitone (dimensionSubgroup R G) := by
  intro m n h g hg
  exact power_antitone R G h hg

instance dimensionSubgroup_normal (n : ℕ) : (dimensionSubgroup R G n).Normal where
  conj_mem g hg h := by
    change delta R (h*g*h⁻¹) - 1 ∈ power R G n
    have he : delta R (h*g*h⁻¹) - 1 = delta R h * (delta R g - 1) * delta R h⁻¹ := by
      simp [mul_sub, sub_mul, mul_assoc]
    rw [he]
    exact mul_mem_right R G n _ _ (mul_mem_left R G n _ _ hg)

variable {H : Type*} [Group H]

/-- A group homomorphism induces the usual map of group algebras. -/
def induced (f : G →* H) : A R G →ₐ[R] A R H :=
  MonoidAlgebra.mapDomainAlgHom R R f

@[simp] theorem induced_delta (f : G →* H) (g : G) :
    induced R G f (delta R g) = delta R (f g) := by
  simp [induced, delta]

@[simp] theorem augmentation_induced (f : G →* H) (a : A R G) :
    augmentation R H (induced R G f a) = augmentation R G a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g r => simp [induced]

/-- Functoriality of every actual augmentation power. -/
theorem induced_mem_power (f : G →* H) (n : ℕ) (a : A R G)
    (ha : a ∈ power R G n) : induced R G f a ∈ power R H n := by
  induction n generalizing a with
  | zero => trivial
  | succ n ih =>
    induction ha using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hv
      rw [map_mul]
      exact mul_mem_succ R H (ih _ hx) (by simpa using hy)
    | zero => simp
    | add x y _ _ hx hy => simpa using (power R H (n+1)).add_mem hx hy
    | smul r x _ hx => simpa using (power R H (n+1)).smul_mem r hx

/-- A group homomorphism preserves all augmentation dimension subgroups. -/
theorem map_dimensionSubgroup_le (f : G →* H) (n : ℕ) :
    (dimensionSubgroup R G n).map f ≤ dimensionSubgroup R H n := by
  rintro g ⟨h, hh, rfl⟩
  have ht := induced_mem_power R G f n (delta R h - 1) hh
  simpa using ht

end UnitDistance.GroupAugmentation
