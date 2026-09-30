module

public import UnitDistance.SIntegerLocalMeasure
public import UnitDistance.IdealPlaneProjection
public import UnitDistance.EuclideanIdealFundamentalDomain

@[expose] public section
set_option backward.privateInPublic true


/-! # Fundamental domains of the actual diagonal S-integers -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain WithZero MeasureTheory

namespace UnitDistance.SIntegerCRT

open RelativeIdealCosets

variable {K : Type} [Field K] [NumberField K]
  {T : Type*} [Fintype T]

/-- The actual ideal lattice's half-open archimedean parallelepiped. -/
abbrev idealArchDomain (I : IdealGroup K) : Set (EuclideanIdeal.Space K) :=
  EuclideanIdeal.idealFundamentalDomain K I

theorem idealArchDomain_unique (I : IdealGroup K) (x : EuclideanIdeal.Space K) :
    ∃! l : EuclideanIdeal.lattice K I, (l : EuclideanIdeal.Space K) + x ∈ idealArchDomain I := by
  have h := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((Module.Free.chooseBasis ℤ (EuclideanIdeal.lattice K I)).ofZLatticeBasis ℝ) x
  rw [(Module.Free.chooseBasis ℤ (EuclideanIdeal.lattice K I)).ofZLatticeBasis_span ℝ] at h
  exact h

theorem idealArchDomain_measurable (I : IdealGroup K) : MeasurableSet (idealArchDomain I) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem idealArchDomain_bounded (I : IdealGroup K) : Bornology.IsBounded (idealArchDomain I) :=
  ZSpan.fundamentalDomain_isBounded _

theorem idealArchDomain_volume (I : IdealGroup K) :
    volume.real (idealArchDomain I) = ZLattice.covolume (EuclideanIdeal.lattice K I) := by
  rw [EuclideanIdeal.covolume_lattice]
  exact EuclideanIdeal.idealFundamentalDomain_volumeReal K I

/-- A field-element form of the actual ideal lattice's unique reduction. -/
theorem idealArchDomain_unique_field (I : IdealGroup K) (x : EuclideanIdeal.Space K) :
    ∃! z : I.val, EuclideanIdeal.embedding K (z : K) + x ∈ idealArchDomain I := by
  obtain ⟨l, hl, hu⟩ := idealArchDomain_unique I x
  refine ⟨(EuclideanIdeal.idealLatticeEquiv K I).symm l, ?_, ?_⟩
  · simpa only [← EuclideanIdeal.idealLatticeEquiv_coe, AddEquiv.apply_symm_apply] using hl
  · intro z hz
    apply (EuclideanIdeal.idealLatticeEquiv K I).injective
    rw [AddEquiv.apply_symm_apply]
    exact hu _ hz

/-- The actual diagonal map on S-integers, with Euclidean archimedean coordinates. -/
def diagonalEmbedding (P : T → HeightOneSpectrum (𝓞 K)) :
    (Set.range P).integer K →+ EuclideanIdeal.Space K × LocalProduct P where
  toFun x := (EuclideanIdeal.embedding K x.val, localEmbedding P x.val)
  map_zero' := by simp [EuclideanIdeal.embedding]
  map_add' x y := by
    apply Prod.ext
    · exact EuclideanIdeal.embedding_add K x.val y.val
    · exact map_add (localEmbedding P) x.val y.val

@[simp] theorem diagonalEmbedding_fst (P : T → HeightOneSpectrum (𝓞 K))
    (x : (Set.range P).integer K) : (diagonalEmbedding P x).1 = EuclideanIdeal.embedding K x.val := rfl

@[simp] theorem diagonalEmbedding_snd (P : T → HeightOneSpectrum (𝓞 K))
    (x : (Set.range P).integer K) : (diagonalEmbedding P x).2 = localEmbedding P x.val := rfl

/-- The actual diagonal S-integer additive subgroup. -/
def diagonalSIntegers (P : T → HeightOneSpectrum (𝓞 K)) :
    AddSubgroup (EuclideanIdeal.Space K × LocalProduct P) := (diagonalEmbedding P).range

/-- The actual product domain associated to the finite period. -/
def productDomain (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    Set (EuclideanIdeal.Space K × LocalProduct P) :=
  idealArchDomain (periodIdeal P a) ×ˢ (finitePeriod P a)

/-- Every ambient point is reduced uniquely into the product domain by an
actual S-integer. The finite reduction is the proved CRT construction. -/
theorem productDomain_unique_sInteger (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (a : T → ℤ)
    (x : EuclideanIdeal.Space K × LocalProduct P) :
    ∃! y : (Set.range P).integer K, diagonalEmbedding P y + x ∈ productDomain P a := by
  obtain ⟨y, hy⟩ := exists_sInteger_in_finitePeriod_coset P hP a (-x.2)
  have hyf : localEmbedding P (y : K) + x.2 ∈ finitePeriod P a := by simpa using hy
  obtain ⟨z, hz, hu⟩ := idealArchDomain_unique_field (periodIdeal P a)
    (EuclideanIdeal.embedding K (y : K) + x.1)
  have hzi := (mem_periodIdeal_iff P hP a (z : K)).mp z.property
  let zS : (Set.range P).integer K := ⟨z, hzi.1⟩
  refine ⟨zS + y, ?_, ?_⟩
  · constructor
    · change EuclideanIdeal.embedding K ((zS : K) + (y : K)) + x.1 ∈ _
      rw [EuclideanIdeal.embedding_add, add_assoc]
      exact hz
    · change localEmbedding P ((zS : K) + (y : K)) + x.2 ∈ finitePeriod P a
      rw [map_add, add_assoc]
      exact (finitePeriod P a).add_mem hzi.2 hyf
  · intro w hw
    have hwf : localEmbedding P (w : K) + x.2 ∈ finitePeriod P a := hw.2
    have hdiff : localEmbedding P ((w : K) - (y : K)) ∈ finitePeriod P a := by
      simpa only [map_sub, add_sub_add_right_eq_sub] using (finitePeriod P a).sub_mem hwf hyf
    have hi : (w : K) - (y : K) ∈ (periodIdeal P a).val :=
      (mem_periodIdeal_iff P hP a _).mpr ⟨((Set.range P).integer K).sub_mem w.property y.property, hdiff⟩
    have harch : EuclideanIdeal.embedding K ((w : K) - (y : K)) +
        (EuclideanIdeal.embedding K (y : K) + x.1) ∈ idealArchDomain (periodIdeal P a) := by
      have he : EuclideanIdeal.embedding K ((w : K) - (y : K)) +
          EuclideanIdeal.embedding K (y : K) = EuclideanIdeal.embedding K (w : K) := by
        rw [← EuclideanIdeal.embedding_add, sub_add_cancel]
      simpa only [Prod.fst_add, diagonalEmbedding_fst, ← add_assoc, he] using hw.1
    have heq := congrArg (fun q : (periodIdeal P a).val ↦ (q : K)) (hu ⟨_, hi⟩ harch)
    apply Subtype.ext
    change (w : K) = (z : K) + (y : K)
    exact sub_eq_iff_eq_add.mp heq

local instance semiLocalMeasurableSpace (P : T → HeightOneSpectrum (𝓞 K)) (t : T) :
    MeasurableSpace ((P t).adicCompletion K) := borel ((P t).adicCompletion K)
local instance semiLocalBorelSpace (P : T → HeightOneSpectrum (𝓞 K)) (t : T) :
    BorelSpace ((P t).adicCompletion K) := ⟨rfl⟩

/-- Actual product Haar measure with ordinary Euclidean measure at infinity. -/
def semiLocalHaar (P : T → HeightOneSpectrum (𝓞 K)) :
    Measure (EuclideanIdeal.Space K × LocalProduct P) := volume.prod (localProductHaar P)

theorem diagonalEmbedding_injective (P : T → HeightOneSpectrum (𝓞 K)) :
    Function.Injective (diagonalEmbedding P) := by
  intro x y h
  apply Subtype.ext
  exact EuclideanIdeal.embedding_injective K (congrArg Prod.fst h)

/-- Exact unique reduction for the literal diagonal subgroup. -/
theorem productDomain_unique (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (a : T → ℤ)
    (x : EuclideanIdeal.Space K × LocalProduct P) :
    ∃! g : diagonalSIntegers P, g +ᵥ x ∈ productDomain P a := by
  obtain ⟨y, hy, hu⟩ := productDomain_unique_sInteger P hP a x
  refine ⟨⟨diagonalEmbedding P y, ⟨y, rfl⟩⟩, hy, ?_⟩
  intro g hg
  obtain ⟨w, hw⟩ := g.property
  have hw' : diagonalEmbedding P w + x ∈ productDomain P a := by
    rw [hw]
    exact hg
  apply Subtype.ext
  exact hw.symm.trans (congrArg (diagonalEmbedding P) (hu w hw'))

/-- The actual product parallelepiped and finite rectangle form a fundamental
domain for the actual diagonal S-integers. -/
theorem productDomain_fundamental (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (a : T → ℤ) :
    IsAddFundamentalDomain (diagonalSIntegers P) (productDomain P a) (semiLocalHaar P) := by
  apply IsAddFundamentalDomain.mk'
  · exact ((idealArchDomain_measurable _).prod (finitePeriod_measurable P a)).nullMeasurableSet
  · exact productDomain_unique P hP a

/-- The product domain has the exact number-field discriminant volume,
independent of every signed local period exponent. -/
theorem productDomain_volume (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    (semiLocalHaar P).real (productDomain P a) =
      (2⁻¹ : ℝ)^NumberField.InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)| := by
  rw [semiLocalHaar, productDomain, measureReal_prod_prod, idealArchDomain_volume,
    EuclideanIdeal.covolume_lattice, finitePeriod_volume_eq_inv_norm]
  have hn : (FractionalIdeal.absNorm (periodIdeal P a).val : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr (periodIdeal P a).ne_zero)
  field_simp [hn]

/-- The actual diagonal S-integers are discrete in the archimedean and
selected finite completions. -/
theorem diagonalSIntegers_discreteTopology (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) : DiscreteTopology (diagonalSIntegers P) := by
  let a : T → ℤ := fun _ ↦ 0
  let I := periodIdeal P a
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp
    (isOpen_discrete ({0} : Set (EuclideanIdeal.lattice K I)))
  have h0U : (0 : EuclideanIdeal.Space K) ∈ U := by
    have hh : (0 : EuclideanIdeal.lattice K I) ∈
        ((↑) : EuclideanIdeal.lattice K I → EuclideanIdeal.Space K) ⁻¹' U := by
      rw [hUeq]
      exact Set.mem_singleton 0
    exact hh
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have hopen : IsOpen (((↑) : diagonalSIntegers P →
      EuclideanIdeal.Space K × LocalProduct P) ⁻¹' (U ×ˢ (finitePeriod P a))) :=
    (hU.prod (finitePeriod_open P a)).preimage continuous_subtype_val
  convert hopen using 1
  ext g
  constructor
  · intro hg
    have hg0 : g = 0 := Set.mem_singleton_iff.mp hg
    subst g
    exact ⟨h0U, (finitePeriod P a).zero_mem⟩
  · rintro ⟨hgU, hgf⟩
    obtain ⟨y, hy⟩ := g.property
    have hyI : (y : K) ∈ I.val := (mem_periodIdeal_iff P hP a _).mpr
      ⟨y.property, by
        change localEmbedding P (y : K) ∈ (finitePeriod P a : Set (LocalProduct P))
        simpa only [← hy, diagonalEmbedding_snd] using hgf⟩
    let l := EuclideanIdeal.idealLatticeEquiv K I ⟨y, hyI⟩
    have hlU : (l : EuclideanIdeal.Space K) ∈ U := by
      change EuclideanIdeal.embedding K (y : K) ∈ U
      simpa only [← hy, diagonalEmbedding_fst] using hgU
    have hl0 : l = 0 := by
      have hh : l ∈ ((↑) : EuclideanIdeal.lattice K I → EuclideanIdeal.Space K) ⁻¹' U := hlU
      rw [hUeq] at hh
      exact Set.mem_singleton_iff.mp hh
    have hy0 : y = 0 := by
      apply Subtype.ext
      apply EuclideanIdeal.embedding_injective K
      have he := congrArg (fun q : EuclideanIdeal.lattice K I ↦ (q : EuclideanIdeal.Space K)) hl0
      have he0 : EuclideanIdeal.embedding K (y : K) = 0 := by simpa [l] using he
      simpa [EuclideanIdeal.embedding] using he0
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    change (g : EuclideanIdeal.Space K × LocalProduct P) = 0
    rw [← hy, hy0, map_zero]

end UnitDistance.SIntegerCRT
