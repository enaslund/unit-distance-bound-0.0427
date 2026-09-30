module

public import UnitDistance.ArithmeticCatalogRadicands
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual integral catalog elements and finite ramification support

Each catalog radicand has an actual integral complement with integer product
supported on the six primes dividing30030. The same is true of every catalog
word by multiplication of these actual identities.
-/
noncomputable section
namespace UnitDistance.ArithmeticCatalog
open ArithmeticChosenGenus NormExtensionCatalog NumberField
open scoped NumberField

/-- An actual integral complementary factor whose product has support in Σ. -/
def HasSigmaComplement {R : Type*} [CommRing R] (a : R) : Prop :=
  ∃ b : R, ∃ n : ℤ, ∃ m : ℕ, a*b=(n : R) ∧ n ∣ (30030 : ℤ)^m

namespace HasSigmaComplement
variable {R : Type*} [CommRing R]

theorem one : HasSigmaComplement (1 : R) :=
  ⟨1,1,0,by simp,by simp⟩

theorem mul {a b : R} (ha : HasSigmaComplement a) (hb : HasSigmaComplement b) :
    HasSigmaComplement (a*b) := by
  obtain ⟨a',n,m,ha,hn⟩ := ha
  obtain ⟨b',n',m',hb,hn'⟩ := hb
  refine ⟨a'*b',n*n',m+m',?_,?_⟩
  · rw [Int.cast_mul,← ha,← hb]
    ring
  · rw [pow_add]
    exact mul_dvd_mul hn hn'

theorem map {S : Type*} [CommRing S] (f : R →+* S) {a : R}
    (ha : HasSigmaComplement a) : HasSigmaComplement (f a) := by
  obtain ⟨b,n,m,hab,hn⟩ := ha
  refine ⟨f b,n,m,?_,hn⟩
  simpa only [map_mul,map_intCast] using congrArg f hab

theorem pow {a : R} (ha : HasSigmaComplement a) (n : ℕ) :
    HasSigmaComplement (a^n) := by
  induction n with
  | zero => simpa using (one (R := R))
  | succ n ih => simpa only [pow_succ] using ih.mul ha

theorem finset_prod {ι : Type*} (s : Finset ι) (a : ι → R)
    (ha : ∀ i ∈ s, HasSigmaComplement (a i)) : HasSigmaComplement (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (R := R))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (ha i (by simp)).mul (ih fun j hj => ha j (by simp [hj]))

end HasSigmaComplement

theorem rootsA_isIntegral (i : Fin 17) : IsIntegral ℤ (rootsA i) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [rootsA_sq]
  exact isIntegral_intCast (catalog i).A

theorem catalogAlpha_isIntegral (i : Fin 17) : IsIntegral ℤ (catalogAlpha i) := by
  exact (isIntegral_intCast (catalog i).x).add
    ((isIntegral_intCast (catalog i).y).mul (rootsA_isIntegral i))

theorem catalogConjugate_isIntegral (i : Fin 17) :
    IsIntegral ℤ (alpha i (-(rootsA i))) := by
  exact (isIntegral_intCast (catalog i).x).add
    ((isIntegral_intCast (catalog i).y).mul (rootsA_isIntegral i).neg)

/-- The actual catalog radicand as an algebraic integer. -/
def catalogInteger (i : Fin 17) : 𝓞 GenusField :=
  ⟨catalogAlpha i,catalogAlpha_isIntegral i⟩

/-- Its actual conjugate complementary algebraic integer. -/
def catalogComplement (i : Fin 17) : 𝓞 GenusField :=
  ⟨alpha i (-(rootsA i)),catalogConjugate_isIntegral i⟩

theorem catalogInteger_product (i : Fin 17) :
    catalogInteger i*catalogComplement i =
      ((catalog i).B*(catalog i).z^2 : ℤ) := by
  apply Subtype.ext
  change alpha i (rootsA i)*alpha i (-(rootsA i)) =
    (((catalog i).B*(catalog i).z^2 : ℤ) : GenusField)
  simpa only [Int.cast_mul,Int.cast_pow] using alpha_norm i (rootsA i) (rootsA_sq i)

/-- An exact finite support certificate for all seventeen norm products. -/
theorem catalog_norm_divides_sigma_cube (i : Fin 17) :
    (catalog i).B*(catalog i).z^2 ∣ (30030 : ℤ)^3 := by
  have h : ∀ i : Fin 17, (catalog i).B*(catalog i).z^2 ∣ (30030 : ℤ)^3 := by
    decide +kernel
  exact h i

theorem catalogInteger_hasSigmaComplement (i : Fin 17) :
    HasSigmaComplement (catalogInteger i) :=
  ⟨catalogComplement i,(catalog i).B*(catalog i).z^2,3,
    catalogInteger_product i,catalog_norm_divides_sigma_cube i⟩

/-- Every actual raw catalog word is an algebraic integer. -/
def wordInteger (m : ℕ) : 𝓞 GenusField :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin 17 => m.testBit i.val), catalogInteger i

theorem wordInteger_coe (m : ℕ) : (wordInteger m : GenusField)=wordRadicand m := by
  change algebraMap (𝓞 GenusField) GenusField
      (∏ i ∈ Finset.univ.filter (fun i : Fin 17 => m.testBit i.val), catalogInteger i) = _
  rw [map_prod]
  simp [wordRadicand,radicand,catalogInteger,catalogAlpha]

theorem wordInteger_hasSigmaComplement (m : ℕ) : HasSigmaComplement (wordInteger m) :=
  HasSigmaComplement.finset_prod _ _ (fun i _ => catalogInteger_hasSigmaComplement i)

end UnitDistance.ArithmeticCatalog
