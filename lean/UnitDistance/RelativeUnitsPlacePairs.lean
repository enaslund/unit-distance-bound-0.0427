module

public import UnitDistance.RelativeUnitsPlaces

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual infinite-place pairs in a totally complex quadratic extension

These are the coordinate fibers used by the relative regulator. A real base
place has one complex extension place; a complex base place has two, exchanged
by the actual quadratic automorphism.
-/

noncomputable section
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

omit [NumberField K] in
/-- Restriction of places is invariant under the actual quadratic automorphism. -/
theorem comap_involution_smul (ι : K ≃ₐ[F] K) (v : InfinitePlace K) :
    (ι • v).comap (algebraMap F K) = v.comap (algebraMap F K) :=
  (mem_orbit_iff.mp ⟨ι, rfl⟩).symm

/-- Every quadratic infinite-place fiber is exactly an automorphism orbit. -/
theorem comap_eq_iff_eq_or_involution (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v w : InfinitePlace K) :
    w.comap (algebraMap F K) = v.comap (algebraMap F K) ↔ w = v ∨ w = ι • v := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := exists_smul_eq_of_comap_eq h.symm
    rcases automorphism_eq_one_or ι hι g with rfl | rfl
    · exact Or.inl (by simpa using hg.symm)
    · exact Or.inr hg.symm
  · rintro (rfl | rfl)
    · rfl
    · exact comap_involution_smul ι v

omit [NumberField F] [NumberField K] [Algebra.IsQuadraticExtension F K] in
/-- Above a complex base place the two actual extension places are distinct. -/
theorem involution_smul_ne_of_complex_comap (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : InfinitePlace K) (hv : IsComplex (v.comap (algebraMap F K))) : ι • v ≠ v := by
  intro he
  have hu : v.IsUnramified F := isUnramified_iff.mpr (Or.inr hv)
  have hm : ι ∈ MulAction.stabilizer (K ≃ₐ[F] K) v := he
  rw [hu.stabilizer_eq_bot] at hm
  exact hι hm

variable [IsTotallyComplex K]

/-- Above a real base place, the quadratic automorphism fixes the unique
complex place, because it acts as conjugation on its embedding. -/
theorem involution_smul_eq_of_real_comap (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : InfinitePlace K) (hv : IsReal (v.comap (algebraMap F K))) : ι • v = v := by
  have hram : v.IsRamified F := isRamified_iff.mpr ⟨IsTotallyComplex.isComplex v, hv⟩
  obtain ⟨g, hg⟩ := exists_isConj_of_isRamified
    (show IsRamified F (mk v.embedding) by rw [mk_embedding]; exact hram)
  have hgne : g ≠ 1 := (ComplexEmbedding.isConj_ne_one_iff hg).mpr
    (isComplex_iff.mp (IsTotallyComplex.isComplex v))
  have hgι : g = ι := (automorphism_eq_one_or ι hι g).resolve_left hgne
  rw [hgι] at hg
  have hm : ι ∈ MulAction.stabilizer (K ≃ₐ[F] K) (mk v.embedding) :=
    (mem_stabilizer_mk_iff _ _).mpr (Or.inr hg)
  simpa only [mk_embedding, MulAction.mem_stabilizer_iff] using hm

/-- Uniqueness of the complex extension place of an actual real base place. -/
theorem place_above_real_unique (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v w : InfinitePlace K) (hv : IsReal (v.comap (algebraMap F K)))
    (hw : w.comap (algebraMap F K) = v.comap (algebraMap F K)) : w = v := by
  rcases (comap_eq_iff_eq_or_involution ι hι v w).mp hw with h | h
  · exact h
  · rw [h, involution_smul_eq_of_real_comap ι hι v hv]

omit [IsTotallyComplex K] [NumberField F] [NumberField K]
  [Algebra.IsQuadraticExtension F K] in
/-- Choose an actual extension place; existence is the embedding extension theorem. -/
def chosenPlaceAbove [Algebra.IsAlgebraic F K] (w : InfinitePlace F) : InfinitePlace K :=
  Classical.choose (comap_surjective (K := K) w)

omit [IsTotallyComplex K] [NumberField F] [NumberField K]
  [Algebra.IsQuadraticExtension F K] in
@[simp] theorem chosenPlaceAbove_comap [Algebra.IsAlgebraic F K] (w : InfinitePlace F) :
    (chosenPlaceAbove (K := K) w).comap (algebraMap F K) = w :=
  Classical.choose_spec (comap_surjective (K := K) w)

/-- The actual base real places and the two labeled extensions of each complex place. -/
abbrev PairedPlaceIndex (F : Type) [Field F] :=
  {w : InfinitePlace F // IsReal w} ⊕ ({w : InfinitePlace F // IsComplex w} × Bool)

/-- Coordinate labeling by chosen extension places and their actual conjugate partners. -/
def pairedPlace (ι : K ≃ₐ[F] K) : PairedPlaceIndex F → InfinitePlace K
  | Sum.inl w => chosenPlaceAbove w.val
  | Sum.inr (w, false) => chosenPlaceAbove w.val
  | Sum.inr (w, true) => ι • chosenPlaceAbove w.val

/-- The underlying base place of a paired coordinate. -/
def pairedBase : PairedPlaceIndex F → InfinitePlace F
  | Sum.inl w => w.val
  | Sum.inr (w, _) => w.val

omit [IsTotallyComplex K] in
@[simp] theorem pairedPlace_comap (ι : K ≃ₐ[F] K) (a : PairedPlaceIndex F) :
    (pairedPlace ι a).comap (algebraMap F K) = pairedBase a := by
  rcases a with w | ⟨w, b⟩
  · exact chosenPlaceAbove_comap w.val
  · cases b
    · exact chosenPlaceAbove_comap w.val
    · exact (comap_involution_smul ι _).trans (chosenPlaceAbove_comap w.val)

/-- The coordinate labeling exhausts every actual infinite place. -/
theorem pairedPlace_surjective (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Function.Surjective (pairedPlace ι) := by
  intro v
  let w := v.comap (algebraMap F K)
  rcases isReal_or_isComplex w with hw | hw
  · refine ⟨Sum.inl ⟨w, hw⟩, ?_⟩
    exact place_above_real_unique ι hι v (chosenPlaceAbove w) hw (chosenPlaceAbove_comap w)
  · have hf : v.comap (algebraMap F K) =
        (chosenPlaceAbove (K := K) w).comap (algebraMap F K) :=
      (chosenPlaceAbove_comap w).symm
    rcases (comap_eq_iff_eq_or_involution ι hι (chosenPlaceAbove w) v).mp hf with h | h
    · exact ⟨Sum.inr (⟨w, hw⟩, false), h.symm⟩
    · exact ⟨Sum.inr (⟨w, hw⟩, true), h.symm⟩

omit [IsTotallyComplex K] in
/-- A real coordinate occurs once and each complex coordinate occurs in a
pair of distinct actual places. -/
theorem pairedPlace_injective (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Function.Injective (pairedPlace ι) := by
  intro a b hab
  have hw := congrArg (fun v : InfinitePlace K ↦ v.comap (algebraMap F K)) hab
  rw [pairedPlace_comap, pairedPlace_comap] at hw
  rcases a with a | ⟨a, x⟩ <;> rcases b with b | ⟨b, y⟩
  · exact congrArg Sum.inl (Subtype.ext hw)
  · change a.val = b.val at hw
    exact False.elim ((not_isReal_iff_isComplex.mpr b.prop) (hw ▸ a.prop))
  · change a.val = b.val at hw
    exact False.elim ((not_isReal_iff_isComplex.mpr a.prop) (hw.symm ▸ b.prop))
  · have habase : a = b := Subtype.ext hw
    subst b
    have hc : IsComplex ((chosenPlaceAbove (K := K) a.val).comap (algebraMap F K)) := by
      rw [chosenPlaceAbove_comap]
      exact a.prop
    have hn := involution_smul_ne_of_complex_comap ι hι (chosenPlaceAbove a.val) hc
    cases x <;> cases y
    · rfl
    · exact False.elim (hn hab.symm)
    · exact False.elim (hn hab)
    · rfl

/-- The actual quadratic infinite places have precisely the paper's real-plus-
paired-complex indexing, with the second member obtained by its automorphism. -/
def pairedPlaceEquiv (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    PairedPlaceIndex F ≃ InfinitePlace K :=
  Equiv.ofBijective (pairedPlace ι) ⟨pairedPlace_injective ι hι, pairedPlace_surjective ι hι⟩

@[simp] theorem pairedPlaceEquiv_apply (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (a : PairedPlaceIndex F) :
    pairedPlaceEquiv ι hι a = pairedPlace ι a := rfl

omit [IsTotallyComplex K] in
/-- The place action by the quadratic involution has the expected pointwise form. -/
theorem involution_smul_apply (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : InfinitePlace K) (x : K) : (ι • v) x = v (ι x) := by
  rw [InfinitePlace.smul_apply]
  congr 1
  apply ι.injective
  rw [ι.apply_symm_apply, quadratic_automorphism_involutive ι hι]

omit [IsTotallyComplex K] in
/-- The ordinary absolute value of an actual relative norm is the product at
its two automorphism places, with repetitions at ramified infinite places. -/
theorem place_norm_eq_mul (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : InfinitePlace K) (x : K) :
    (v.comap (algebraMap F K)) (Algebra.norm F x) = v x * (ι • v) x := by
  change v (algebraMap F K (Algebra.norm F x)) = _
  rw [norm_eq_mul_involution ι hι, map_mul, involution_smul_apply ι hι]

omit [IsTotallyComplex K] in
/-- The actual logarithmic norm is the sum at the automorphism pair. -/
theorem log_place_norm_eq_add (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : InfinitePlace K) (u : (𝓞 K)ˣ) :
    Real.log ((v.comap (algebraMap F K)) (unitNorm (F := F) u)) =
      Real.log (v u) + Real.log ((ι • v) u) := by
  rw [coe_unitNorm, place_norm_eq_mul ι hι,
    Real.log_mul (Units.pos_at_place _ _).ne' (Units.pos_at_place _ _).ne']

/-- Weighted norm coordinates above a real place have exactly the ordinary
single complex-place coordinate of the extension. -/
theorem weighted_log_norm_real (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (w : {w : InfinitePlace F // IsReal w}) (u : (𝓞 K)ˣ) :
    (mult w.val : ℝ) * Real.log (w.val (unitNorm (F := F) u)) =
      (mult (chosenPlaceAbove (K := K) w.val) : ℝ) *
        Real.log (chosenPlaceAbove (K := K) w.val u) := by
  have h := log_place_norm_eq_add ι hι (chosenPlaceAbove w.val) u
  rw [chosenPlaceAbove_comap,
    involution_smul_eq_of_real_comap ι hι _ (by rw [chosenPlaceAbove_comap]; exact w.prop)] at h
  rw [mult_isReal w, IsTotallyComplex.mult_eq]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  linarith

/-- Weighted norm coordinates above a complex place are the sum of its two
ordinary weighted extension coordinates. -/
theorem weighted_log_norm_complex (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (w : {w : InfinitePlace F // IsComplex w}) (u : (𝓞 K)ˣ) :
    (mult w.val : ℝ) * Real.log (w.val (unitNorm (F := F) u)) =
      (mult (chosenPlaceAbove (K := K) w.val) : ℝ) *
          Real.log (chosenPlaceAbove (K := K) w.val u) +
        (mult (ι • chosenPlaceAbove (K := K) w.val) : ℝ) *
          Real.log ((ι • chosenPlaceAbove (K := K) w.val) u) := by
  have h := log_place_norm_eq_add ι hι (chosenPlaceAbove w.val) u
  rw [chosenPlaceAbove_comap] at h
  rw [mult_isComplex w, IsTotallyComplex.mult_eq, IsTotallyComplex.mult_eq]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  linarith

end UnitDistance.RelativeUnits
