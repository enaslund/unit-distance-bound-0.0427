module

public import UnitDistance.Sqrt241.DyadicLink.Kummer
public import UnitDistance.Sqrt241.Cut.Basic
public import UnitDistance.Sqrt241.Generators.Source

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The Kummer map factors through the retained quotient (dyadic link, steps 3–4)

**Finite check (step 3).** Coordinate 13 of the retained cocycle `Retained.cocycle` is
exactly `v₅ w₃` (`retained_cocycle_thirteen`, from `retainedCocycleMasks`). In the
language of the universal class-two layer `F₂³⁶`: coordinate 27 (the pair `(3,5)`,
i.e. the quadratic form `x₃x₅`) vanishes on the 21 cut initials
(`relationVector_pair35`), the universal cocycle has coordinate 27 equal to `v₅ w₃`
(`universal_cocycle_pair35`), and `Retained.reduction` sends coordinate 27 to
coordinate 13 (`reduction_thirteen`). Hence `retainedToKummer c : (v, w) ↦
(v, w₁₃ + ⟨c, v⟩)` is a homomorphism `Retained.Q →* KummerQ` for every twist `c`.

**Comparison (step 4).** With `c = genChar` (the Kummer signs of the chosen generators
`gen i`), `kummerMap ∘ freeMap` and `retainedToKummer genChar ∘ Cut.retainedFree` are
continuous homomorphisms from the free pro-2 group on eight generators that agree on
the generators, hence are equal (`kummerMap_freeMap`). Consequently every `f` with
`retainedFree f = 1` has `freeMap f` fixing `√β₁` (`freeMap_fixes_sqrtBeta`), and the
same holds for the kernel of any retained map `ρ : G_B →ₜ* Q_B` with
`ρ ∘ freeMap = retainedFree` (`fixes_sqrtBeta_of_retained`).
-/

open scoped NumberField

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.DyadicLink

open Tower ClassTwo GroupData ProCGroups ProCGroups.ProC ProCGroups.FreeProC

/-! ### Step 3: the finite check -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem retained_cocycle_certificate : ∀ i j : Fin 8,
    Retained.cocycle (Pi.single i 1) (Pi.single j 1) 13 =
      kummerForm (Pi.single i 1) (Pi.single j 1) := by
  decide +kernel

/-- **Coordinate 13 of the retained law is the Kummer form** `v₅ w₃`. -/
theorem retained_cocycle_thirteen (v w : V) : Retained.cocycle v w 13 = v 5 * w 3 := by
  have h : Retained.cocycle.compr₂ (LinearMap.proj 13) = kummerForm := by
    apply linearMap_ext_single
    intro i
    apply linearMap_ext_single
    intro j
    exact retained_cocycle_certificate i j
  have h' := congrArg (fun φ : V →ₗ[F] V →ₗ[F] F => φ v w) h
  simpa using h'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The functional `x₃x₅` (universal coordinate 27, the pair `(3,5)`) vanishes on the
21 quadratic cut initials. -/
theorem relationVector_pair35 : ∀ i : Fin 21, Retained.relationVector i 27 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem universal_cocycle_certificate : ∀ i j : Fin 8,
    Universal.cocycle (Pi.single i 1) (Pi.single j 1) 27 =
      kummerForm (Pi.single i 1) (Pi.single j 1) := by
  decide +kernel

/-- Coordinate 27 of the universal law is `v₅ w₃`. -/
theorem universal_cocycle_pair35 (v w : V) : Universal.cocycle v w 27 = v 5 * w 3 := by
  have h : Universal.cocycle.compr₂ (LinearMap.proj 27) = kummerForm := by
    apply linearMap_ext_single
    intro i
    apply linearMap_ext_single
    intro j
    exact universal_cocycle_certificate i j
  have h' := congrArg (fun φ : V →ₗ[F] V →ₗ[F] F => φ v w) h
  simpa using h'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem reduction_certificate : ∀ k : Fin 36,
    Retained.reduction (Pi.single k 1) 13 = (Pi.single k (1 : F) : Universal.W) 27 := by
  decide +kernel

/-- The reduction sends the pair `(3,5)` coordinate to retained coordinate 13. -/
theorem reduction_thirteen (w : Universal.W) : Retained.reduction w 13 = w 27 := by
  have h : (LinearMap.proj 13).comp Retained.reduction =
      (LinearMap.proj 27 : Universal.W →ₗ[F] F) := by
    apply linearMap_ext_single
    intro k
    exact reduction_certificate k
  have h' := congrArg (fun φ : Universal.W →ₗ[F] F => φ w) h
  simpa using h'

/-! ### The twisted homomorphism `Q_B → KummerQ` -/

/-- `Φ_c : Q_B →* KummerQ`, `(v, w) ↦ (v, w₁₃ + ⟨c, v⟩)`. -/
def retainedToKummer (c : V) : Retained.Q →* KummerQ where
  toFun q := ⟨q.base, q.central 13 + ∑ i, c i * q.base i⟩
  map_one' := by
    apply GroupModel.ext
    · rfl
    · change (0 : Retained.W) 13 + ∑ i, c i * (0 : V) i = 0
      simp
  map_mul' q r := by
    apply GroupModel.ext
    · rfl
    · change (q.central + r.central + Retained.cocycle q.base r.base) 13 +
          ∑ i, c i * (q.base + r.base) i =
        (q.central 13 + ∑ i, c i * q.base i) + (r.central 13 + ∑ i, c i * r.base i) +
          kummerForm q.base r.base
      rw [Pi.add_apply, Pi.add_apply, retained_cocycle_thirteen, kummerForm_apply]
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring

theorem retainedToKummer_continuous (c : V) : Continuous (retainedToKummer c) :=
  continuous_of_discreteTopology

/-- The Kummer signs of the chosen generators `gen i` of `G_B`. -/
def genChar : V := fun i => kummerChar (gen i)

theorem kummerMap_gen (i : Fin 8) : kummerMap (gen i) = ⟨Pi.single i 1, genChar i⟩ := by
  apply GroupModel.ext
  · rw [kummerMap_base, gen_label]
    rfl
  · rfl

theorem retainedToKummer_single (c : V) (i : Fin 8) :
    retainedToKummer c ⟨Pi.single i 1, 0⟩ = ⟨Pi.single i 1, c i⟩ := by
  apply GroupModel.ext
  · rfl
  · change (0 : Retained.W) 13 + ∑ j, c j * (Pi.single i (1 : F) : V) j = c i
    simp [Pi.single_apply]

/-! ### Step 4: the comparison -/

/-- **`Ψ ∘ freeMap = Φ_c ∘ retainedFree`.** -/
theorem kummerMap_freeMap (f : Cut.Source) :
    kummerMap (freeMap f) = retainedToKummer genChar (Cut.retainedFree f) := by
  have h := (FiniteFreeProTwo.isFree 8).hom_ext kummerQ_hasPGroupOpenNormalBasis
    (f := (kummerMap.comp freeMap).toMonoidHom)
    (g := (retainedToKummer genChar).comp Cut.retainedFree.toMonoidHom)
    (kummerMap.comp freeMap).continuous
    ((retainedToKummer_continuous genChar).comp Cut.retainedFree.continuous)
    (fun i => by
      change kummerMap (freeMap (FiniteFreeProTwo.generator 8 i)) =
        retainedToKummer genChar (Cut.retainedFree (FiniteFreeProTwo.generator 8 i))
      rw [freeMap_generator, Cut.retainedFree_generator, kummerMap_gen,
        retainedToKummer_single])
  exact DFunLike.congr_fun h f

/-- **`retainedFree f = 1 ⇒ freeMap f` fixes `√β₁`.** -/
theorem freeMap_fixes_sqrtBeta (f : Cut.Source) (hf : Cut.retainedFree f = 1) :
    ((freeMap f : GB) : Ghat) tOm = tOm := by
  apply fixes_tOm_of_kummerMap_eq_one
  rw [kummerMap_freeMap, hf, map_one]

/-- **The kernel of any retained map fixes `√β₁`**: if `ρ : G_B →ₜ* Q_B` satisfies
`ρ ∘ freeMap = retainedFree` (`Retained.Input.retainedMap`, `Retained.Input.retainedMap_freeMap`),
every `g ∈ G_B` with `ρ g = 1` fixes `√β₁`. -/
theorem fixes_sqrtBeta_of_retained (ρ : GB →* Retained.Q)
    (hρ : ∀ f : Cut.Source, ρ (freeMap f) = Cut.retainedFree f) {g : GB} (hg : ρ g = 1) :
    (g : Ghat) tOm = tOm := by
  obtain ⟨f, rfl⟩ := freeMap_surjective g
  exact freeMap_fixes_sqrtBeta f (by rw [← hρ f, hg])

end UnitDistance.Sqrt241.DyadicLink
