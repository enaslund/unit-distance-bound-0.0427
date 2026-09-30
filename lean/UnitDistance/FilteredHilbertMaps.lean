module

public import UnitDistance.FilteredHilbert

@[expose] public section
set_option backward.privateInPublic true


/-!
# Hilbert values of actual filtered submodule maps

Subspaces use the induced ambient filtration. Inclusions increase Hilbert
values for nonnegative parameters, and filtration-preserving maps cannot
increase the Hilbert value of any actual subspace on the unit interval.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.FilteredHilbert
variable (K V W : Type*) [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Restricting the ambient filtration to the subtype does not change the
actual dimensions or its Hilbert value. -/
theorem value_comap_subtype (F : ℕ → Submodule K V) (U : Submodule K V)
    (N : ℕ) (t : ℝ) :
    value K U (fun n => (F n).comap U.subtype) N t =
      value K V (fun n => U ⊓ F n) N t := by
  have hdim (n : ℕ) : Module.finrank K ↥((F n).comap U.subtype) =
      Module.finrank K ↥(U ⊓ F n) := by
    have h := (Submodule.comapSubtypeEquivOfLe (inf_le_left : U ⊓ F n ≤ U)).finrank_eq
    have hc : U.comap U.subtype = ⊤ := Submodule.comap_subtype_self U
    rw [Submodule.comap_inf, hc, top_inf_eq] at h
    exact h
  simp only [value,hdim]

/-- An actual induced subspace has no larger Hilbert value than a containing
induced subspace. This follows from strict additivity for the quotient map. -/
theorem value_induced_mono (F : ℕ → Submodule K V) (hF : Antitone F)
    (U Z : Submodule K V) (hUZ : U ≤ Z) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    value K V (fun n => U ⊓ F n) N t ≤
      value K V (fun n => Z ⊓ F n) N t := by
  have he := value_map_add_kernel K V (V ⧸ U) (fun n => Z ⊓ F n) U.mkQ N t
  have hk (n : ℕ) : (Z ⊓ F n) ⊓ U.mkQ.ker = U ⊓ F n := by
    rw [Submodule.ker_mkQ]
    ext a
    simp only [Submodule.mem_inf]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hUZ h.1,h.2⟩,h.1⟩⟩
  simp only [hk] at he
  have hn := value_nonneg K (V ⧸ U) (fun n => (Z ⊓ F n).map U.mkQ)
    (fun _ _ h => Submodule.map_mono (inf_le_inf_left Z (hF h))) N t ht
  linarith

/-- Filtration-preserving maps do not increase the Hilbert value of the
image of any actual source subspace, with both induced filtrations. -/
theorem value_induced_map_le (F : ℕ → Submodule K V) (G : ℕ → Submodule K W)
    (hF : Antitone F) (hF0 : F 0 = ⊤) (hG0 : G 0 = ⊤)
    (f : V →ₗ[K] W) (hmap : ∀ n, (F n).map f ≤ G n)
    (U : Submodule K V) (N : ℕ) (hFN : F N = ⊥) (hGN : G N = ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value K W (fun n => U.map f ⊓ G n) N t ≤
      value K V (fun n => U ⊓ F n) N t := by
  let fU := f.comp U.subtype
  have hUmap (n : ℕ) : ((F n).comap U.subtype).map fU ≤ G n := by
    rintro y ⟨x,hx,rfl⟩
    exact hmap n ⟨x.1,hx,rfl⟩
  have hU0 : (F 0).comap U.subtype = ⊤ := by rw [hF0,Submodule.comap_top]
  have hUN : (F N).comap U.subtype = ⊥ := by
    rw [hFN,Submodule.comap_bot,LinearMap.ker_eq_bot.mpr U.injective_subtype]
  have he := value_induced_range_le K U W (fun n => (F n).comap U.subtype) G
    (fun _ _ h => Submodule.comap_mono (hF h)) hU0 hG0 fU hUmap N hUN hGN t ht0 ht1
  have hr : fU.range = U.map f := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
  rw [hr,value_comap_subtype] at he
  exact he

end UnitDistance.FilteredHilbert
