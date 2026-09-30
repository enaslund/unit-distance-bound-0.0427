module

public import UnitDistance.LatticePacking
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exponential sums over genuinely separated points

The finite shell counts are proved by Haar packing. A floor partition and
geometric series then bound the entire nonzero exponential mass, including
its summability. No shell-count or Fourier-tail hypothesis is used.
-/
noncomputable section
open Module
open scoped Classical
namespace UnitDistance.Packing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def shellIndex (R : ℝ) (x : E) : ℕ := ⌊‖x‖/R⌋₊

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem shell_lower {R : ℝ} (hR : 0 < R) (x : E) :
    (shellIndex R x : ℝ)*R ≤ ‖x‖ :=
  (le_div_iff₀ hR).mp (Nat.floor_le (by positivity))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem shell_upper {R : ℝ} (hR : 0 < R) (x : E) :
    ‖x‖ < ((shellIndex R x : ℝ)+1)*R :=
  (div_lt_iff₀ hR).mp (Nat.lt_floor_add_one (‖x‖/R))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem shellIndex_pos {R : ℝ} (hR : 0 < R) (x : E) (hx : R ≤ ‖x‖) :
    1 ≤ shellIndex R x := by
  apply (Nat.one_le_floor_iff _).mpr
  exact (le_div_iff₀ hR).mpr (by simpa using hx)

def packingRatio (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R σ : ℝ) : ℝ := (5:ℝ)^finrank ℝ E * Real.exp (-σ*R)

omit [FiniteDimensional ℝ E] in
theorem packingRatio_pos (R σ : ℝ) : 0 < packingRatio E R σ := by
  unfold packingRatio
  positivity

/-- The complete finite exponential sum, with the zero shell absent because
all points have norm at least the actual separation radius. -/
theorem sum_exp_le (s : Finset E) {R σ : ℝ} (hR : 0 < R) (hσ : 0 ≤ σ)
    (hmin : ∀ x ∈ s, R ≤ ‖x‖)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → R ≤ ‖x-y‖)
    (hq : packingRatio E R σ < 1) :
    ∑ x ∈ s, Real.exp (-σ*‖x‖) ≤
      packingRatio E R σ / (1-packingRatio E R σ) := by
  let J := s.image (shellIndex R)
  let q := packingRatio E R σ
  have hq0 : 0 < q := packingRatio_pos R σ
  have hj : ∀ j ∈ J, 1 ≤ j := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
    exact shellIndex_pos hR x (hmin x hx)
  have hfinite : ∑ x ∈ s, Real.exp (-σ*‖x‖) ≤ ∑ j ∈ J, q^j := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := J) (g := shellIndex R) (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      (fun x => Real.exp (-σ*‖x‖))]
    apply Finset.sum_le_sum
    intro j hjJ
    let u := s.filter (fun x => shellIndex R x = j)
    have hu : ∀ x ∈ u, ‖x‖ ≤ (j+1)*R := by
      intro x hx
      obtain ⟨_, hxj⟩ := Finset.mem_filter.mp hx
      simpa only [hxj] using (shell_upper hR x).le
    have hcard := card_shell_le_five u hR j (hj j hjJ) hu
      (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
    calc
      ∑ x ∈ u, Real.exp (-σ*‖x‖) ≤ ∑ _x ∈ u, Real.exp (-σ*((j:ℝ)*R)) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Real.exp_le_exp.mpr
        have hxj := (Finset.mem_filter.mp hx).2
        have hlo := shell_lower hR x
        rw [hxj] at hlo
        nlinarith
      _ = (u.card : ℝ)*Real.exp (-σ*((j:ℝ)*R)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (5:ℝ)^(finrank ℝ E*j)*Real.exp (-σ*((j:ℝ)*R)) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = q^j := by
        dsimp only [q, packingRatio]
        rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
        congr 2
        ring
  have hz : 0 ∉ J := by
    intro h
    have := hj 0 h
    omega
  have hqn : ‖q‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_pos hq0] using hq
  have hgeom := hasSum_geometric_of_norm_lt_one hqn
  have hg := Summable.sum_le_tsum (insert 0 J) (fun _ _ => pow_nonneg hq0.le _)
    hgeom.summable
  rw [Finset.sum_insert hz, pow_zero, hgeom.tsum_eq] at hg
  have he : q/(1-q) = (1-q)⁻¹-1 := by
    have hn : 1-q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
    field_simp
    ring
  change _ ≤ q/(1-q)
  rw [he]
  linarith

/-- An indexed version, proving convergence for any injective family of
separated nonzero points. This avoids assuming a lattice enumeration. -/
theorem summable_exp_and_tsum_le_of_injective {ι : Type*} (f : ι → E)
    (hinj : Function.Injective f) {R σ : ℝ} (hR : 0 < R) (hσ : 0 ≤ σ)
    (hmin : ∀ x, R ≤ ‖f x‖)
    (hsep : ∀ x y, x ≠ y → R ≤ ‖f x-f y‖)
    (hq : packingRatio E R σ < 1) :
    Summable (fun x => Real.exp (-σ*‖f x‖)) ∧
      (∑' x, Real.exp (-σ*‖f x‖)) ≤ packingRatio E R σ/(1-packingRatio E R σ) := by
  have hf : ∀ u : Finset ι, ∑ x ∈ u, Real.exp (-σ*‖f x‖) ≤
      packingRatio E R σ/(1-packingRatio E R σ) := by
    intro u
    let e : ι ↪ E := ⟨f, hinj⟩
    have h := sum_exp_le (u.map e) hR hσ
      (by intro x hx; obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx; exact hmin a)
      (by intro x hx y hy hxy
          obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
          exact hsep a b (fun h => hxy (congrArg f h))) hq
    simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk] using h
  exact ⟨summable_of_sum_le (fun _ => (Real.exp_pos _).le) hf,
    Real.tsum_le_of_sum_le (fun _ => (Real.exp_pos _).le) hf⟩

/-- A bound for an arbitrary separated set, with convergence proved from the
finite sums. It applies directly to the nonzero part of an actual lattice. -/
theorem summable_exp_and_tsum_le (S : Set E) {R σ : ℝ} (hR : 0 < R) (hσ : 0 ≤ σ)
    (hmin : ∀ x ∈ S, R ≤ ‖x‖)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → R ≤ ‖x-y‖)
    (hq : packingRatio E R σ < 1) :
    Summable (fun x : S => Real.exp (-σ*‖(x:E)‖)) ∧
      (∑' x : S, Real.exp (-σ*‖(x:E)‖)) ≤ packingRatio E R σ/(1-packingRatio E R σ) := by
  have hf : ∀ u : Finset S, ∑ x ∈ u, Real.exp (-σ*‖(x:E)‖) ≤
      packingRatio E R σ/(1-packingRatio E R σ) := by
    intro u
    let e : S ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
    have h := sum_exp_le (u.map e) hR hσ
      (by intro x hx; obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx; exact hmin a a.2)
      (by intro x hx y hy hxy
          obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
          exact hsep a a.2 b b.2 hxy) hq
    simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk] using h
  exact ⟨summable_of_sum_le (fun _ => (Real.exp_pos _).le) hf,
    Real.tsum_le_of_sum_le (fun _ => (Real.exp_pos _).le) hf⟩

end UnitDistance.Packing
