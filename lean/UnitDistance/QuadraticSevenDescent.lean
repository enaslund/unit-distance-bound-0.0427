module

public import UnitDistance.QuadraticRadicalPresentation
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
set_option backward.privateInPublic true


/-! A real quadratic radical in a totally complex quadratic extension
already belongs to every base field having a real place. The proof builds
an actual real embedding if the radical is nonsquare in the base. -/
noncomputable section
namespace UnitDistance.QuadraticSeven
open NumberField QuadraticAlgebra KummerInvariant
variable {F K : Type*} [Field F] [CharZero F] [Field K] [Algebra F K]

/-- A quadratic algebra has an actual real embedding whenever the base
embedding carries its radicand to an actual real square. -/
def realRadicalHom (φ : F →+* ℝ) (a : F) (t : ℝ) (ht : t^2=φ a) :
    Extension a →+* ℝ := by
  letI : Algebra F ℝ := φ.toAlgebra
  exact (QuadraticAlgebra.lift ⟨t,by
    simp only [Algebra.smul_def,map_zero,zero_mul,mul_one,add_zero]
    change t*t=φ a
    simpa only [pow_two] using ht⟩).toRingHom

/-- No totally complex field has an actual real embedding. -/
theorem false_of_realEmbedding [IsTotallyComplex K] (ψ : K →+* ℝ) : False := by
  apply IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp ψ)
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

/-- Positivity at a real base embedding forces a displayed quadratic radical
to descend through an actual totally complex extension of relative degree two. -/
theorem root_descends_of_real_square [IsTotallyComplex K]
    (φ : F →+* ℝ) (a : F) (t : ℝ) (ht : t^2=φ a)
    (r : K) (hr : r^2=algebraMap F K a) (hd : Module.finrank F K=2) :
    ∃ s : F, s^2=a := by
  by_contra h
  have ha : Nonsquare a := by
    intro s hs
    exact h ⟨s,hs⟩
  letI : Fact (Nonsquare a) := ⟨ha⟩
  let e := QuadraticRadical.equiv a r hr hd
  exact false_of_realEmbedding ((realRadicalHom φ a t ht).comp e.symm.toRingHom)

/-- The actual square root of seven descends, without choosing the base field
as a particular fixed-field construction. -/
theorem exists_root_of_totallyComplex_quadratic [IsTotallyComplex K]
    (φ : F →+* ℝ) (r : K) (hr : r^2=7) (hd : Module.finrank F K=2) :
    ∃ s : F, s^2=7 := by
  apply root_descends_of_real_square φ (7 : F) (Real.sqrt 7) _ r _ hd
  · simpa only [map_ofNat] using Real.sq_sqrt (by norm_num : (0 : ℝ)≤7)
  · simpa only [map_ofNat] using hr

/-- A real infinite place suffices for the same actual descent. -/
theorem exists_root_of_real_place [IsTotallyComplex K]
    (w : InfinitePlace F) (hw : w.IsReal)
    (r : K) (hr : r^2=7) (hd : Module.finrank F K=2) :
    ∃ s : F, s^2=7 :=
  exists_root_of_totallyComplex_quadratic (InfinitePlace.embedding_of_isReal hw) r hr hd

/-- Positive real-place count gives the exact frontend used by the arithmetic target. -/
theorem exists_root_of_positive_real_places [NumberField F] [IsTotallyComplex K]
    (hreal : 0<InfinitePlace.nrRealPlaces F) (r : K) (hr : r^2=7) (hd : Module.finrank F K=2) :
    ∃ s : F, s^2=7 := by
  classical
  have hn : Nonempty {w : InfinitePlace F // w.IsReal} := Fintype.card_pos_iff.mp hreal
  obtain ⟨w,hw⟩ := hn
  exact exists_root_of_real_place w hw r hr hd

end UnitDistance.QuadraticSeven
