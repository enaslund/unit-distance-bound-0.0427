module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option backward.privateInPublic true


/-!
# Finite filtered Hilbert values, maps and intersections

Values are defined from actual successive subspace dimensions. Telescoping
proves monotonicity under filtration-preserving surjections without a
strictness assumption, and proves the intersection correction for actual
subspaces. These are the finite filtered linear-algebra inequalities used
in the weighted Golod--Shafarevich contradiction.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.FilteredHilbert
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Actual successive dimensions; for an antitone filtration each
coefficient is the dimension of its actual successive quotient. -/
def value (F : ℕ → Submodule K V) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ((Module.finrank K ↥(F n) : ℝ) - Module.finrank K ↥(F (n+1))) * t^n

omit [FiniteDimensional K V] in
/-- An elementary finite summation identity keeps the terminal error term
explicit, before applying any filtration termination hypothesis. -/
theorem telescoping (d : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range N, (d n-d (n+1))*t^n) =
      d 0 - (1-t)*(∑ n ∈ Finset.range N, d (n+1)*t^n) - d N*t^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih,pow_succ]
    ring

theorem value_eq_cumulative (F : ℕ → Submodule K V) (N : ℕ) (hN : F N = ⊥) (t : ℝ) :
    value K V F N t = (Module.finrank K ↥(F 0) : ℝ) -
      (1-t)*(∑ n ∈ Finset.range N, (Module.finrank K ↥(F (n+1)) : ℝ)*t^n) := by
  rw [value,telescoping,hN,finrank_bot]
  simp

/-- Removing the first filtration degree gives the usual Hilbert shift. -/
theorem value_succ (F : ℕ → Submodule K V) (N : ℕ) (t : ℝ) :
    value K V F (N+1) t =
      ((Module.finrank K ↥(F 0) : ℝ) - Module.finrank K ↥(F 1)) +
        t * value K V (fun n => F (n+1)) N t := by
  unfold value
  rw [Finset.sum_range_succ',Finset.mul_sum]
  simp only [pow_zero,mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [pow_succ]
  ring

/-- Repeating the initial stage shifts the actual Hilbert value by one. -/
theorem value_shift (F : ℕ → Submodule K V) (N : ℕ) (t : ℝ) :
    value K V (fun n => F (n-1)) (N+1) t = t * value K V F N t := by
  rw [value_succ]
  simp

/-- Appending a zero terminal layer changes no Hilbert value. -/
theorem value_extend (F : ℕ → Submodule K V) (N : ℕ)
    (hN : F N = ⊥) (hN1 : F (N+1) = ⊥) (t : ℝ) :
    value K V F (N+1) t = value K V F N t := by
  unfold value
  rw [Finset.sum_range_succ,hN,hN1,finrank_bot]
  simp

/-- Any finite degree shift multiplies the actual Hilbert value by its
corresponding power. -/
theorem value_shift_add (F : ℕ → Submodule K V) (N s : ℕ) (t : ℝ) :
    value K V (fun n => F (n-s)) (N+s) t = t^s * value K V F N t := by
  induction s with
  | zero => simp
  | succ s ih =>
    have he : (fun n => F (n-(s+1))) = (fun n => (fun k => F (k-s)) (n-1)) := by
      funext n
      congr 1
      omega
    rw [he,Nat.add_succ,value_shift K V (fun k => F (k-s)) (N+s) t,ih,pow_succ]
    ring

/-- Once every later stage is zero, the truncation cutoff may be extended. -/
theorem value_extend_of_le (F : ℕ → Submodule K V) (N M : ℕ) (hNM : N ≤ M)
    (hzero : ∀ n, N ≤ n → F n = ⊥) (t : ℝ) :
    value K V F M t = value K V F N t := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hM ih =>
    rw [value_extend K V F M (hzero M hM) (hzero (M+1) (by omega)),ih]

/-- At a fixed common initial space, enlarging every filtration stage
reduces its Hilbert value on `[0,1]`. -/
theorem value_le_of_stage_le (F G : ℕ → Submodule K V)
    (h0 : F 0 = G 0) (hFG : ∀ n, F n ≤ G n)
    (N : ℕ) (hFN : F N = ⊥) (hGN : G N = ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value K V G N t ≤ value K V F N t := by
  rw [value_eq_cumulative K V F N hFN,value_eq_cumulative K V G N hGN,h0]
  apply sub_le_sub_left
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht1)
  apply Finset.sum_le_sum
  intro n _
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht0 n)
  exact_mod_cast Submodule.finrank_mono (hFG (n+1))

theorem value_nonneg (F : ℕ → Submodule K V) (hF : Antitone F)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ value K V F N t := by
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg
  · exact sub_nonneg.mpr (by exact_mod_cast Submodule.finrank_mono (hF (Nat.le_succ n)))
  · positivity

variable (W : Type*) [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Rank-nullity restricted to an actual subspace, expressed as dimensions
of its image and intersection with the actual map kernel. -/
theorem finrank_map_add_inf_ker (f : V →ₗ[K] W) (U : Submodule K V) :
    Module.finrank K ↥(U.map f) + Module.finrank K ↥(U ⊓ f.ker) = Module.finrank K U := by
  let g := f.comp U.subtype
  have hr : g.range = U.map f := by
    rw [LinearMap.range_comp]
    simp
  have hk : g.ker = (U ⊓ f.ker).comap U.subtype := by
    ext x
    simp [g]
  have he := g.finrank_range_add_finrank_ker
  rw [hr,hk,(Submodule.comapSubtypeEquivOfLe (inf_le_left : U ⊓ f.ker ≤ U)).finrank_eq] at he
  exact he

/-- A map whose image filtration is contained in the target filtration
loses no more Hilbert value than its actual induced kernel accounts for.
No strictness of the map is required. -/
theorem value_le_sub_kernel_of_surjective
    (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hF0 : F 0 = ⊤) (hG0 : G 0 = ⊤)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (hmap : ∀ n, (F n).map f ≤ G n)
    (N : ℕ) (hFN : F N = ⊥) (hGN : G N = ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value K W G N t ≤ value K V F N t - value K V (fun n => F n ⊓ f.ker) N t := by
  have hKN : F N ⊓ f.ker = ⊥ := by rw [hFN,bot_inf_eq]
  rw [value_eq_cumulative K W G N hGN,value_eq_cumulative K V F N hFN,
    value_eq_cumulative K V (fun n => F n ⊓ f.ker) N hKN]
  have hzero : (Module.finrank K ↥(G 0) : ℝ) + Module.finrank K ↥(F 0 ⊓ f.ker) =
      Module.finrank K ↥(F 0) := by
    have he := finrank_map_add_inf_ker K V W f (F 0)
    have hr : (F 0).map f = G 0 := by
      rw [hF0,hG0,Submodule.map_top,LinearMap.range_eq_top.mpr hf]
    rw [hr] at he
    exact_mod_cast he
  have hsum :
      (∑ n ∈ Finset.range N, (Module.finrank K ↥(F (n+1)) : ℝ)*t^n) ≤
        (∑ n ∈ Finset.range N, (Module.finrank K ↥(G (n+1)) : ℝ)*t^n) +
        (∑ n ∈ Finset.range N, (Module.finrank K ↥(F (n+1) ⊓ f.ker) : ℝ)*t^n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    have he := finrank_map_add_inf_ker K V W f (F (n+1))
    have hle := Submodule.finrank_mono (hmap (n+1))
    have hd : (Module.finrank K ↥(F (n+1)) : ℝ) ≤
        Module.finrank K ↥(G (n+1)) + Module.finrank K ↥(F (n+1) ⊓ f.ker) := by
      exact_mod_cast (show Module.finrank K ↥(F (n+1)) ≤
        Module.finrank K ↥(G (n+1)) + Module.finrank K ↥(F (n+1) ⊓ f.ker) by omega)
    simpa only [add_mul] using mul_le_mul_of_nonneg_right hd (pow_nonneg ht0 n)
  have hh := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr ht1)
  linarith

/-- Filtration-preserving surjections decrease the actual Hilbert value
on `[0,1]`, even if their image filtration is not the induced filtration. -/
theorem value_le_of_surjective
    (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hF : Antitone F) (hF0 : F 0 = ⊤) (hG0 : G 0 = ⊤)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (hmap : ∀ n, (F n).map f ≤ G n)
    (N : ℕ) (hFN : F N = ⊥) (hGN : G N = ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value K W G N t ≤ value K V F N t := by
  have he := value_le_sub_kernel_of_surjective K V W F G hF0 hG0 f hf hmap N hFN hGN t ht0 ht1
  have hk := value_nonneg K V (fun n => F n ⊓ f.ker)
    (fun _ _ h => inf_le_inf_right _ (hF h)) N t ht0
  linarith

/-- Strict maps are additive with their actual induced kernel, degree by
degree, so the corresponding Hilbert values are exactly additive. -/
theorem value_map_add_kernel (F : ℕ → Submodule K V) (f : V →ₗ[K] W) (N : ℕ) (t : ℝ) :
    value K W (fun n => (F n).map f) N t +
      value K V (fun n => F n ⊓ f.ker) N t = value K V F N t := by
  unfold value
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have h₀ : (Module.finrank K ↥((F n).map f) : ℝ) + Module.finrank K ↥(F n ⊓ f.ker) =
      Module.finrank K ↥(F n) := by exact_mod_cast finrank_map_add_inf_ker K V W f (F n)
  have h₁ : (Module.finrank K ↥((F (n+1)).map f) : ℝ) + Module.finrank K ↥(F (n+1) ⊓ f.ker) =
      Module.finrank K ↥(F (n+1)) := by exact_mod_cast finrank_map_add_inf_ker K V W f (F (n+1))
  dsimp only
  rw [← h₀,← h₁]
  ring

/-- The actual image subspace, with its induced ambient filtration,
has no greater Hilbert value than a filtration-preserving source. -/
theorem value_induced_range_le (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hF : Antitone F) (hF0 : F 0 = ⊤) (hG0 : G 0 = ⊤)
    (f : V →ₗ[K] W) (hmap : ∀ n, (F n).map f ≤ G n)
    (N : ℕ) (hFN : F N = ⊥) (hGN : G N = ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value K W (fun n => f.range ⊓ G n) N t ≤ value K V F N t := by
  have h0 : (F 0).map f = f.range ⊓ G 0 := by
    rw [hF0,hG0,Submodule.map_top,inf_top_eq]
  have hs (n : ℕ) : (F n).map f ≤ f.range ⊓ G n :=
    le_inf (by rw [← Submodule.map_top]; exact Submodule.map_mono le_top) (hmap n)
  have he := value_le_of_stage_le K W (fun n => (F n).map f) (fun n => f.range ⊓ G n)
    h0 hs N (by rw [hFN,Submodule.map_bot]) (by rw [hGN,inf_bot_eq]) t ht0 ht1
  have ha := value_map_add_kernel K V W F f N t
  have hk := value_nonneg K V (fun n => F n ⊓ f.ker)
    (fun _ _ h => inf_le_inf_right _ (hF h)) N t ht0
  linarith

/-- The intersection with a fixed ambient filtration stage is a
supermodular dimension function on actual subspaces. -/
theorem finrank_inf_sup_le (U Z S : Submodule K V) :
    Module.finrank K ↥(U ⊓ S) + Module.finrank K ↥(Z ⊓ S) ≤
      Module.finrank K ↥((U ⊔ Z) ⊓ S) + Module.finrank K ↥((U ⊓ Z) ⊓ S) := by
  have hle : (U ⊓ S) ⊔ (Z ⊓ S) ≤ (U ⊔ Z) ⊓ S :=
    sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  have hi : (U ⊓ S) ⊓ (Z ⊓ S) = (U ⊓ Z) ⊓ S := by
    ext a
    simp only [Submodule.mem_inf]
    tauto
  have he := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ S) (Z ⊓ S)
  rw [hi] at he
  have hd := Submodule.finrank_mono hle
  omega

/-- The actual common subspace is subtracted once from the sum of the
two filtered costs. No quotient is assumed to embed into an ambient kernel. -/
theorem value_sup_add_inf_le (F : ℕ → Submodule K V) (hF0 : F 0 = ⊤)
    (U Z : Submodule K V) (N : ℕ) (hFN : F N = ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value K V (fun n => (U ⊔ Z) ⊓ F n) N t +
      value K V (fun n => (U ⊓ Z) ⊓ F n) N t ≤
      value K V (fun n => U ⊓ F n) N t + value K V (fun n => Z ⊓ F n) N t := by
  have hN (S : Submodule K V) : S ⊓ F N = ⊥ := by rw [hFN,inf_bot_eq]
  rw [value_eq_cumulative K V _ N (hN (U ⊔ Z)),value_eq_cumulative K V _ N (hN (U ⊓ Z)),
    value_eq_cumulative K V _ N (hN U),value_eq_cumulative K V _ N (hN Z)]
  have hzero : (Module.finrank K ↥((U ⊔ Z) ⊓ F 0) : ℝ) + Module.finrank K ↥((U ⊓ Z) ⊓ F 0) =
      Module.finrank K ↥(U ⊓ F 0) + Module.finrank K ↥(Z ⊓ F 0) := by
    rw [hF0,inf_top_eq,inf_top_eq,inf_top_eq,inf_top_eq]
    exact_mod_cast Submodule.finrank_sup_add_finrank_inf_eq U Z
  have hsum :
      (∑ n ∈ Finset.range N, (Module.finrank K ↥(U ⊓ F (n+1)) : ℝ)*t^n) +
        (∑ n ∈ Finset.range N, (Module.finrank K ↥(Z ⊓ F (n+1)) : ℝ)*t^n) ≤
      (∑ n ∈ Finset.range N, (Module.finrank K ↥((U ⊔ Z) ⊓ F (n+1)) : ℝ)*t^n) +
        (∑ n ∈ Finset.range N, (Module.finrank K ↥((U ⊓ Z) ⊓ F (n+1)) : ℝ)*t^n) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    have hd : (Module.finrank K ↥(U ⊓ F (n+1)) : ℝ) + Module.finrank K ↥(Z ⊓ F (n+1)) ≤
        Module.finrank K ↥((U ⊔ Z) ⊓ F (n+1)) + Module.finrank K ↥((U ⊓ Z) ⊓ F (n+1)) := by
      exact_mod_cast finrank_inf_sup_le K V U Z (F (n+1))
    simpa only [add_mul] using mul_le_mul_of_nonneg_right hd (pow_nonneg ht0 n)
  have hh := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr ht1)
  linarith

/-- The usual subadditivity is a consequence of the stronger actual
intersection correction and nonnegativity of the intersection layers. -/
theorem value_sup_le (F : ℕ → Submodule K V) (hF : Antitone F) (hF0 : F 0 = ⊤)
    (U Z : Submodule K V) (N : ℕ) (hFN : F N = ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value K V (fun n => (U ⊔ Z) ⊓ F n) N t ≤
      value K V (fun n => U ⊓ F n) N t + value K V (fun n => Z ⊓ F n) N t := by
  have he := value_sup_add_inf_le K V F hF0 U Z N hFN t ht0 ht1
  have hi := value_nonneg K V (fun n => (U ⊓ Z) ⊓ F n)
    (fun _ _ h => inf_le_inf_left _ (hF h)) N t ht0
  linarith

/-- A finite family of actual subspaces costs at most the sum of its
individual induced Hilbert values. -/
theorem value_iSup_le {J : Type*} [Fintype J]
    (F : ℕ → Submodule K V) (hF : Antitone F) (hF0 : F 0 = ⊤)
    (U : J → Submodule K V) (N : ℕ) (hFN : F N = ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value K V (fun n => (⨆ j, U j) ⊓ F n) N t ≤
      ∑ j, value K V (fun n => U j ⊓ F n) N t := by
  classical
  have he (S : Finset J) : value K V (fun n => (⨆ j ∈ S, U j) ⊓ F n) N t ≤
      ∑ j ∈ S, value K V (fun n => U j ⊓ F n) N t := by
    induction S using Finset.induction_on with
    | empty =>
      have hempty : (⨆ j ∈ (∅ : Finset J), U j) = ⊥ := by simp
      rw [hempty]
      simp only [bot_inf_eq]
      simp [value]
    | @insert j S hj ih =>
      rw [Finset.iSup_insert,Finset.sum_insert hj]
      exact (value_sup_le K V F hF hF0 (U j) (⨆ j ∈ S, U j) N hFN t ht0 ht1).trans
        (add_le_add le_rfl ih)
  simpa using he Finset.univ

end UnitDistance.FilteredHilbert
