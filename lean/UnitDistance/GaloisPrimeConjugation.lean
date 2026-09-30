module

public import UnitDistance.GaloisPrimeNormCounts
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! An abelian genus coordinate excludes conjugation from every decomposition
subgroup over a rational prime once it excludes it from one such subgroup. -/
noncomputable section
namespace UnitDistance.GaloisPrimeConjugation
open NumberField IsDedekindDomain NumberFieldAnalysis
open scoped Pointwise

/-- Stabilizers of points in one orbit have the same image in an abelian quotient. -/
theorem stabilizer_image_smul {G X A : Type*} [Group G] [MulAction G X] [CommGroup A]
    (π : G →* A) (g : G) (x : X) :
    (MulAction.stabilizer G (g • x)).map π = (MulAction.stabilizer G x).map π := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply]

variable {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]

/-- The ordinary Galois action on ideals is exactly the map of integers
induced by the actual field automorphism. -/
theorem galois_smul_ideal (c : Gal(K/ℚ)) (P : Ideal (𝓞 K)) :
    c • P = Ideal.map (RingOfIntegers.mapRingHom c.toRingHom) P := by
  rw [Ideal.pointwise_smul_def]
  congr 1

/-- A genuine abelian genus exclusion for one actual prime moves every
actual prime in the corresponding Galois fiber. -/
theorem map_ideal_ne_of_genus_exclusion {A : Type*} [CommGroup A]
    (π : Gal(K/ℚ) →* A) (c : Gal(K/ℚ)) (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 K)) [P.asIdeal.LiesOver (rationalPrimeIdeal p)]
    (hex : π c ∉ (MulAction.stabilizer Gal(K/ℚ) P.asIdeal).map π)
    (f : ℕ) (hf : 0 < f) (Q : PrimeNormFiber K (p^f)) :
    Ideal.map (RingOfIntegers.mapRingHom c.toRingHom) Q.1.asIdeal ≠ Q.1.asIdeal := by
  letI := P.isPrime
  letI := Q.1.isPrime
  have hq := primeNormFiber_liesOver K (Nat.one_lt_pow hf.ne' hp.one_lt) Q
  rw [hp.pow_minFac hf.ne'] at hq
  letI : Q.1.asIdeal.LiesOver (rationalPrimeIdeal p) := hq
  obtain ⟨g,hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (rationalPrimeIdeal p)
    P.asIdeal Q.1.asIdeal Gal(K/ℚ)
  have he : (MulAction.stabilizer Gal(K/ℚ) Q.1.asIdeal).map π =
      (MulAction.stabilizer Gal(K/ℚ) P.asIdeal).map π := by
    rw [←hg]
    exact stabilizer_image_smul π g P.asIdeal
  intro h
  apply hex
  rw [←he]
  exact ⟨c,(galois_smul_ideal c Q.1.asIdeal).trans h,rfl⟩

end UnitDistance.GaloisPrimeConjugation
