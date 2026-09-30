module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section
set_option backward.privateInPublic true


/-!
# Strict injections from a filtered inverse in degree zero

An actual pair of linear maps whose composition differs from the identity
by a filtration-raising map reflects every filtration stage. Nilpotence
then makes the first map injective. This is the coordinate-change argument
needed for local Fox blocks, without asserting a pro-free basis theorem.
-/

noncomputable section
namespace UnitDistance.FilteredLinear
variable (K V W : Type*) [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
variable (f : V →ₗ[K] W) (r : W →ₗ[K] V)

/-- A filtered left inverse modulo one higher filtration degree suffices
to reflect all actual filtration stages. -/
theorem reflects_filtration (hF0 : F 0 = ⊤) (hG : Antitone G)
    (hr : ∀ n, (G n).map r ≤ F n)
    (herror : ∀ n x, x ∈ F n → r (f x)-x ∈ F (n+1))
    (n : ℕ) (x : V) (hx : f x ∈ G n) : x ∈ F n := by
  induction n with
  | zero => rw [hF0]; exact Submodule.mem_top
  | succ n ih =>
    have hxF : x ∈ F n := ih (hG (Nat.le_succ n) hx)
    have hrf : r (f x) ∈ F (n+1) := hr (n+1) ⟨f x,hx,rfl⟩
    have he := (F (n+1)).sub_mem hrf (herror n x hxF)
    simpa only [sub_sub_cancel] using he

/-- Nilpotence upgrades filtration reflection to actual injectivity. -/
theorem injective_of_raises_error (hF0 : F 0 = ⊤) (hG : Antitone G)
    (hr : ∀ n, (G n).map r ≤ F n)
    (herror : ∀ n x, x ∈ F n → r (f x)-x ∈ F (n+1))
    (N : ℕ) (hFN : F N = ⊥) : Function.Injective f := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    have hfx : f x = 0 := hx
    have h := reflects_filtration K V W F G f r hF0 hG hr herror N x
      (by rw [hfx]; exact (G N).zero_mem)
    rwa [hFN] at h
  · exact bot_le

/-- The image filtration of every actual subspace is its induced ambient
filtration once the map preserves and reflects filtration. -/
theorem map_inf_eq (hf : ∀ n, (F n).map f ≤ G n)
    (hreflect : ∀ n x, f x ∈ G n → x ∈ F n)
    (U : Submodule K V) (n : ℕ) :
    (U ⊓ F n).map f = U.map f ⊓ G n := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx.1,rfl⟩,hf n ⟨x,hx.2,rfl⟩⟩
  · rintro y ⟨⟨x,hx,rfl⟩,hy⟩
    exact ⟨x,⟨hx,hreflect n x hy⟩,rfl⟩

end UnitDistance.FilteredLinear
