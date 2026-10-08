module

public import UnitDistance.Sqrt241.V2.Window41
public import UnitDistance.Sqrt241.Geometry.WitnessPrimePairs
public import UnitDistance.RationalGaloisAlgebra
public import UnitDistance.GaloisConjugationFixedField

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: the concrete tower data

`towerDataV2 : V2.TowerData` for the 41-cap tower:

* `M = input.M` (version 1's fixed base, unchanged), with `√3, √−1 ∈ M`;
* `Ks j = level j = Ω^{U_j ∩ detKer}` (`V2/Levels.lean`), `U_j ≤ G_B` open normal containing
  the cut with the cap at `41₁`; `φ j = φ₁|K_j`, `c j = c₁|K_j`;
* `D = input.detectorField`, `cD = c₁|D`, with version 1's centralizer bound `2^16`;
* `K_j / M` unramified at the finite places (`V2/Types.lean`);
* windows `0` at `2, 3, 5, 29` (`V2/Types.lean`) and `√241 − r` at `41` (`V2/Window41.lean`),
  freely moved by `c_j` (`V2/Freedom.lean`).

The `ℚ`-algebra structures of `TowerData` are the canonical `DivisionRing.toRatAlgebra`; the
constructions use the intermediate-field structures, and `RationalGalois` transports between
them, as in version 1's `Levels/Export.lean`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.V2

open Tower Retained UnitDistance.NumberFieldAnalysis NumberField Filter

instance detectorField_numberField : NumberField input.detectorField :=
  NumberField.of_module_finite ℚ _

/-- The canonical automorphisms of the detector field. -/
def detectorAut :
    Gal(input.detectorField/ℚ) ≃* @AlgEquiv ℚ input.detectorField input.detectorField _ _ _
      DivisionRing.toRatAlgebra DivisionRing.toRatAlgebra :=
  RationalGalois.autEquiv input.detectorField _ DivisionRing.toRatAlgebra

/-- `c₁|D`. -/
def detectorConj : @AlgEquiv ℚ input.detectorField input.detectorField _ _ _
    DivisionRing.toRatAlgebra DivisionRing.toRatAlgebra :=
  detectorAut (Input.res input.detectorField cHat)

theorem coe_detectorConj (x : input.detectorField) :
    ((detectorConj x : input.detectorField) : Omega) = cHat (x : Omega) := by
  rw [detectorConj, detectorAut, RationalGalois.autEquiv_apply]
  exact GaloisEmbedding.restriction_commutes input.detectorField.val cHat x

theorem detectorConj_index :
    65536 ≤ (Subgroup.centralizer ({detectorConj} : Set (@AlgEquiv ℚ input.detectorField
      input.detectorField _ _ _ DivisionRing.toRatAlgebra DivisionRing.toRatAlgebra))).index := by
  have h0 := input.centralizer_index input.detectorField
    (le_of_eq input.detectorField_fixingSubgroup)
  have h1 := GaloisConjugation.centralizer_index_le_of_surjective
    detectorAut.symm.toMonoidHom detectorAut.symm.surjective detectorConj
  simp only [MulEquiv.coe_toMonoidHom, detectorConj, MulEquiv.symm_apply_apply] at h1
  exact h0.trans h1

theorem levelConj_ne_id (j : ℕ) : levelConjRing j ≠ RingEquiv.refl _ := by
  intro h
  have h1 := levelConj_rootLevel j 2
  rw [h, RingEquiv.refl_apply] at h1
  have h2 : (2 : level j) * rootLevel j 2 = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero h3
  · have h4 := rootLevel_sq j 2
    rw [h3] at h4
    have h5 : ((dInt 2 : ℤ) : level j) = -1 := by
      change (((-1 : ℤ)) : level j) = -1
      push_cast
      ring
    rw [h5] at h4
    norm_num at h4

/-- The version 2 windows: `0` at `2, 3, 5, 29`, `√241 − r` at `41`. -/
def window (j : ℕ) : Fin 5 → 𝓞 (level j) := ![0, 0, 0, 0, window41 j]

theorem window_liesOver (j : ℕ) (a : Fin 5)
    (P : WindowFiber (level j) (Witness.primeNorm a) (window j a)) :
    P.1.asIdeal.LiesOver (rationalPrimeIdeal (Witness.primes a)) := by
  have hq : 1 < Witness.primeNorm a :=
    Nat.one_lt_pow (Witness.residueDegree_pos a).ne' (Witness.primes_prime a).one_lt
  have h := primeNormFiber_liesOver (level j) hq ⟨P.1, P.2.1⟩
  have hmin : (Witness.primeNorm a).minFac = Witness.primes a :=
    (Witness.primes_prime a).pow_minFac (Witness.residueDegree_pos a).ne'
  simpa only [hmin] using h

/-- **The version 2 tower data** for the 41-cap tower. -/
def towerDataV2 : TowerData where
  M := input.M
  instIsGalois := RationalGalois.isGalois _ _ _ input.M_isGalois
  Ks j := level j
  instAlgebraMK j := algebraOfLe (M_le_level j)
  φ := levelPhi
  c j := (levelConjRing j).toRatAlgEquiv
  hc j := by
    change NumberField.ComplexEmbedding.conjugate _ = _
    apply RingHom.ext
    intro x
    change star (levelPhi j x) = levelPhi j (levelConjRing j x)
    exact (levelConj_isConj j x).symm
  hc1 j := by
    intro h
    apply levelConj_ne_id j
    ext x
    have hx := congrArg (fun e : @AlgEquiv ℚ (level j) (level j) _ _ _ DivisionRing.toRatAlgebra
      DivisionRing.toRatAlgebra => e x) h
    exact congrArg (fun y : level j => ((y : Omega) : CanonicalGenus.Closure)) hx
  D := input.detectorField
  instIsGaloisD := RationalGalois.isGalois _ _ _ input.detectorField_isGalois
  instAlgebraDK j := algebraOfLe (detectorField_le_level j)
  cD := detectorConj
  hcD j x := by
    apply Subtype.ext
    change cHat (x : Omega) = ((detectorConj x : input.detectorField) : Omega)
    rw [coe_detectorConj]
  hindexD := detectorConj_index
  hdegree := level_degree_tendsto.congr (fun j => RationalGalois.finrank_eq _ _ _)
  hunrM j := level_finiteUnramified j
  window := window
  window_fixed j a := by
    fin_cases a
    · exact map_zero _
    · exact map_zero _
    · exact map_zero _
    · exact map_zero _
    · exact levelConjInt_window41 j
  window_count j a := by
    fin_cases a
    · exact (level_window_count_small j 0).trans (RationalGalois.finrank_eq _ _ _)
    · exact (level_window_count_small j 1).trans (RationalGalois.finrank_eq _ _ _)
    · exact (level_window_count_small j 2).trans (RationalGalois.finrank_eq _ _ _)
    · exact (level_window_count_small j 3).trans (RationalGalois.finrank_eq _ _ _)
    · exact (level_window_count_41 j).trans (RationalGalois.finrank_eq _ _ _)
  window_free j a P := by
    have := window_liesOver j a P
    exact level_prime_moved j a P.1.asIdeal
  r3 := input.sqrtThree
  hr3 := input.sqrtThree_sq
  ii := input.sqrtNegOne
  hii := input.sqrtNegOne_sq

theorem towerDataV2_M : towerDataV2.M = input.M := rfl

theorem towerDataV2_Ks (j : ℕ) : towerDataV2.Ks j = level j := rfl

theorem towerDataV2_D : towerDataV2.D = input.detectorField := rfl

end UnitDistance.Sqrt241.V2
