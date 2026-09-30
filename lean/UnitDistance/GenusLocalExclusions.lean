module

public import UnitDistance.RetainedOddLocalModels

@[expose] public section
set_option backward.privateInPublic true


/-! Complex conjugation's genus vector is outside each prescribed finite
decomposition image. These are exact finite coordinate certificates. -/
namespace UnitDistance.RetainedQuadratic
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem odd_conjugation_exclusion_certificate : ∀ (i : Fin 5) (g : OddLocal.D i),
    ∃ k, (oddMapFn i g).base k≠binaryVector 7 1 k := by decide +kernel

theorem odd_conjugation_exclusion (i : Fin 5) (g : OddLocal.D i) :
    (oddMap i g).base≠binaryVector 7 1 := by
  intro h
  obtain ⟨k,hk⟩ := odd_conjugation_exclusion_certificate i g
  exact hk (congrFun ((oddMap_eq_fn i g).symm ▸ h) k)

theorem odd_lifts_conjugation_exclusion (i : Fin 5) (a b : Q) (g : OddLocal.D i) :
    (oddMapOfLifts i a b g).base≠binaryVector 7 1 :=
  odd_conjugation_exclusion i g

theorem dyadic_conjugation_exclusion_certificate : ∀ g : Dyadic.D,
    ∃ k, (dyadicMapFn g).base k≠binaryVector 7 1 k := by decide +kernel

theorem dyadic_conjugation_exclusion (g : Dyadic.D) :
    (dyadicMap g).base≠binaryVector 7 1 := by
  intro h
  obtain ⟨k,hk⟩ := dyadic_conjugation_exclusion_certificate g
  exact hk (congrFun h k)

theorem dyadic_lifts_conjugation_exclusion (a b c : Q) (g : Dyadic.D) :
    (dyadicMapOfLifts a b c g).base≠binaryVector 7 1 :=
  dyadic_conjugation_exclusion g

def extraGenusMasks : Fin 5 → ℕ := ![60,71,57,38,101]

theorem extra_conjugation_exclusion_certificate : ∀ (i : Fin 5) (a : F),
    ∃ k, (a • binaryVector 7 (extraGenusMasks i)) k≠binaryVector 7 1 k := by decide +kernel

theorem extra_conjugation_exclusion (i : Fin 5) (a : F) :
    a • binaryVector 7 (extraGenusMasks i)≠binaryVector 7 1 := by
  intro h
  obtain ⟨k,hk⟩ := extra_conjugation_exclusion_certificate i a
  exact hk (congrFun h k)

end UnitDistance.RetainedQuadratic
