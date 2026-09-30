module

public import UnitDistance.RelativeUnitsCoordinateVolume

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual paired coordinates after deleting a real base place

The first coordinate block consists of the chosen first places above complex
base places. The second consists of the remaining place above each undeleted
base place. Thus the norm is obtained by a triangular shear.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

abbrev ComplexPlaceIndex (F : Type) [Field F] := {w : InfinitePlace F // IsComplex w}

abbrev NormCoordinateIndex (v : InfinitePlace F) := {w : InfinitePlace F // w ≠ v}

/-- The raw coordinate labels before adding the two complex-place coordinates. -/
def rawPairedIndex (v : InfinitePlace F) :
    ComplexPlaceIndex F ⊕ NormCoordinateIndex v → PairedPlaceIndex F
  | Sum.inl w => Sum.inr (w, false)
  | Sum.inr w => if h : IsReal w.val then Sum.inl ⟨w.val, h⟩
      else Sum.inr (⟨w.val, not_isReal_iff_isComplex.mp h⟩, true)

theorem rawPairedIndex_ne (v : {w : InfinitePlace F // IsReal w})
    (a : ComplexPlaceIndex F ⊕ NormCoordinateIndex v.val) :
    rawPairedIndex v.val a ≠ Sum.inl v := by
  rcases a with a | a
  · simp [rawPairedIndex]
  · simp only [rawPairedIndex]
    split_ifs with h
    · intro he
      exact a.prop (congrArg (fun x : {w : InfinitePlace F // IsReal w} ↦ x.val)
        (Sum.inl.inj he))
    · exact Sum.inr_ne_inl

theorem rawPairedIndex_injective (v : InfinitePlace F) :
    Function.Injective (rawPairedIndex v) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (Prod.mk.inj (Sum.inr.inj h)).1
  · simp only [rawPairedIndex] at h
    split_ifs at h <;> simp at h
  · simp only [rawPairedIndex] at h
    split_ifs at h <;> simp at h
  · apply congrArg Sum.inr
    apply Subtype.ext
    have ht (t : NormCoordinateIndex v) :
        pairedBase (rawPairedIndex v (Sum.inr t)) = t.val := by
      dsimp only [rawPairedIndex]
      split_ifs <;> rfl
    exact (ht a).symm.trans ((congrArg pairedBase h).trans (ht b))

/-- Every actual extension place except the deleted one is one of the raw
coordinates, each appearing once. -/
def deletedPairedPlaceEquiv (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) :
    (ComplexPlaceIndex F ⊕ NormCoordinateIndex v.val) ≃
      {w : InfinitePlace K // w ≠ chosenPlaceAbove (K := K) v.val} :=
  Equiv.ofBijective (fun a ↦ ⟨pairedPlace ι (rawPairedIndex v.val a), by
    intro h
    exact rawPairedIndex_ne v a (pairedPlace_injective ι hι h)⟩) (by
    constructor
    · intro a b h
      exact rawPairedIndex_injective v.val
        (pairedPlace_injective ι hι (congrArg Subtype.val h))
    · rintro ⟨w, hw⟩
      obtain ⟨a, ha⟩ := pairedPlace_surjective ι hι w
      rcases a with a | ⟨a, b⟩
      · have hav : a.val ≠ v.val := by
          intro he
          apply hw
          rw [← ha]
          change chosenPlaceAbove (K := K) a.val = chosenPlaceAbove (K := K) v.val
          rw [he]
        refine ⟨Sum.inr ⟨a.val, hav⟩, Subtype.ext ?_⟩
        simpa only [rawPairedIndex, dif_pos a.prop] using ha
      · have hav : a.val ≠ v.val := by
          intro he
          exact (not_isReal_iff_isComplex.mpr a.prop) (he ▸ v.prop)
        cases b
        · exact ⟨Sum.inl a, Subtype.ext ha⟩
        · refine ⟨Sum.inr ⟨a.val, hav⟩, Subtype.ext ?_⟩
          simpa only [rawPairedIndex, dif_neg (not_isReal_iff_isComplex.mpr a.prop)] using ha)

@[simp] theorem deletedPairedPlaceEquiv_apply (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w})
    (a : ComplexPlaceIndex F ⊕ NormCoordinateIndex v.val) :
    (deletedPairedPlaceEquiv ι hι v a).val = pairedPlace ι (rawPairedIndex v.val a) := rfl

/-- The first-place coordinate to add to the second, zero at a real base place. -/
def pairCoordinateAddition (v : InfinitePlace F) :
    (ComplexPlaceIndex F → ℝ) →ₗ[ℝ] (NormCoordinateIndex v → ℝ) where
  toFun x w := if h : IsReal w.val then 0 else x ⟨w.val, not_isReal_iff_isComplex.mp h⟩
  map_add' x y := by ext w; by_cases hw : IsReal w.val <;> simp [hw]
  map_smul' r x := by ext w; by_cases hw : IsReal w.val <;> simp [hw]

end UnitDistance.RelativeUnits
