/-
Generalizes the local radical values of Naganori Yamaguchi's
SawinTotallyRealTowers/RealCharacterInertiaExistence.lean (private, for the
class of `−1` only) to the class of an arbitrary global unit, and the global
reciprocity argument of SawinTotallyRealTowers/NegativeThreeLocalRadical.lean
(ℚ, one real place) to a totally real number field with any number of real
places, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0).
-/
module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.RealCharacterInertiaExistence
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportInertiaCorrection

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Reciprocity values of global quadratic characters on global units

For a number field `F`, a finite place `v`, a local character `χ` of the
decomposition group at `v` and an element `r` of the ideal-square radical,
`localRadicalValueAt F v χ r ∈ ℤ/2` is the local reciprocity pairing of `χ`
with the localization of `r`; the finite-support reciprocity functional of a
family is the sum of these values (`radicalFamily_eq_sum`).

For a global quadratic character `γ` unramified outside a finite set `D` of
finite places and a global unit `u`, global reciprocity gives, over a totally
real `F`,
`∑_{v ∈ D} localRadicalValueAt v (γ|_v) [u] = ∑_{w real, u <_w 0} γ(c_w)`
(`sum_localRadicalValueAt_unit`), where `c_w` is the real Artin element.
-/

open NumberField IsDedekindDomain
open scoped NumberField BigOperators

noncomputable section

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Sawin ClassFieldTower.Martinet.Shafarevich ClassFieldTower.ProP
open GlobalClassFieldTheory.Reciprocity

local instance radicalReciprocityValuative
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ValuativeRel (v.adicCompletion F) := finitePlaceAdicCompletionValuativeRel F v

local instance radicalReciprocityLocalField
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsNonarchimedeanLocalField (v.adicCompletion F) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField F v

local instance radicalReciprocityH1Module
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod 2) (ContinuousH1ZMod (p := 2) (G := G)) := continuousH1ZModModule

local instance radicalReciprocityH1AddCommGroup
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    AddCommGroup (ContinuousH1ZMod (p := 2) (G := G)) :=
  ContinuousAddMonoidHom.instAddCommGroup (Additive G) (ZMod 2)

section LocalValues

variable (F : Type) [Field F] [NumberField F]

/-- The class of a global unit in the ideal-square radical. -/
def radicalUnit (u : (𝓞 F)ˣ) : idealPowerRadicalModP F 2 :=
  Additive.ofMul (integralUnitToIdealNthPowerRadicalQuotient F (2 : ℕ+) u)

theorem radicalUnit_image (u : (𝓞 F)ˣ) :
    idealPowerRadicalToAbsolutePowerClassLinearMap F 2 (radicalUnit F u) =
      Additive.ofMul (QuotientGroup.mk' (powMonoidHom 2 : Fˣ →* Fˣ).range
        (RayClass.integralUnitToFieldUnit u)) := by
  rfl

/-- The local reciprocity value of a local character on a radical class. -/
def localRadicalValueAt (v : HeightOneSpectrum (𝓞 F))
    (χ : ContinuousH1ZMod (p := 2) (G := finitePlaceAbsoluteDecompositionGroup F v))
    (r : idealPowerRadicalModP F 2) : ZMod 2 :=
  localReciprocityH1PowerClassPairing (v.adicCompletion F) 2
    (finitePlaceDecompositionH1ToAdic F 2 v χ)
    (finitePlacePowerClassLocalization F 2 v
      (idealPowerRadicalToAbsolutePowerClassLinearMap F 2 r))

theorem localRadicalValueAt_add (v : HeightOneSpectrum (𝓞 F))
    (χ ψ : ContinuousH1ZMod (p := 2) (G := finitePlaceAbsoluteDecompositionGroup F v))
    (r : idealPowerRadicalModP F 2) :
    localRadicalValueAt F v (χ + ψ) r =
      localRadicalValueAt F v χ r + localRadicalValueAt F v ψ r := by
  unfold localRadicalValueAt
  rw [map_add, map_add]
  rfl

theorem localRadicalValueAt_smul (v : HeightOneSpectrum (𝓞 F)) (a : ZMod 2)
    (χ : ContinuousH1ZMod (p := 2) (G := finitePlaceAbsoluteDecompositionGroup F v))
    (r : idealPowerRadicalModP F 2) :
    localRadicalValueAt F v (a • χ) r = a * localRadicalValueAt F v χ r := by
  unfold localRadicalValueAt
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem localRadicalValueAt_zero (v : HeightOneSpectrum (𝓞 F))
    (r : idealPowerRadicalModP F 2) :
    localRadicalValueAt F v 0 r = 0 := by
  unfold localRadicalValueAt
  rw [map_zero, map_zero, LinearMap.zero_apply]

/-- The restricted finite-support reciprocity functional is the sum of the
local radical values. -/
theorem radicalFamily_eq_sum
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : ∀ v : ↥S, ContinuousH1ZMod (p := 2)
      (G := finitePlaceAbsoluteDecompositionGroup F v.1))
    (r : idealPowerRadicalModP F 2) :
    (absolutePowerClassDualRestriction F 2
      (finiteSupportLocalReciprocityPowerClassFunctional F 2 S
        (fun v => finitePlaceDecompositionH1ToAdic F 2 v.1 (χ v)))) r =
      ∑ v : ↥S, localRadicalValueAt F v.1 (χ v) r := by
  exact finiteSupportLocalReciprocityPowerClassFunctional_apply F 2 S
    (fun v => finitePlaceDecompositionH1ToAdic F 2 v.1 (χ v))
    (idealPowerRadicalToAbsolutePowerClassLinearMap F 2 r)

/-- The local radical value of the restriction of a global character on the
class of a global unit is its global reciprocity value at that place. -/
theorem localRadicalValueAt_absoluteCharacter (v : HeightOneSpectrum (𝓞 F))
    (γ : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2)) (u : (𝓞 F)ˣ) :
    localRadicalValueAt F v
        (h1OfCharacter (γ.comp (finitePlaceAbsoluteDecompositionInclusion F v)))
        (radicalUnit F u) =
      (globalReciprocityIdeleCharacter F 2 γ
        (IdeleGroup.finitePlaceIdele v (IdeleGroup.finiteComponent v
          (IdeleGroup.principalIdele F (RayClass.integralUnitToFieldUnit u))))).toAdd := by
  let χv := finitePlaceAbsoluteH1AdicRestriction F 2 v (Additive.ofMul γ)
  let a : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom
      (RayClass.integralUnitToFieldUnit u)
  have hLoc := (congrArg (fun q : absolutePowerClassModP F 2 =>
    finitePlacePowerClassLocalization F 2 v q) (radicalUnit_image F u)).trans
      (finitePlacePowerClassLocalization_mk F 2 v (RayClass.integralUnitToFieldUnit u))
  have hPair := congrArg (fun q : absolutePowerClassModP (v.adicCompletion F) 2 =>
    localReciprocityH1PowerClassPairing (v.adicCompletion F) 2 χv q) hLoc
  have hEval := localReciprocityH1PowerClassPairing_mk (v.adicCompletion F) 2 χv a
  have hArtin := localReciprocityUnitCharacter_absoluteCharacter F (2 : ℕ+) γ v a
  have hEval' : (localReciprocityH1PowerClassPairing (v.adicCompletion F) 2 χv)
      (finitePlacePowerClassLocalization F 2 v
        (idealPowerRadicalToAbsolutePowerClassLinearMap F 2 (radicalUnit F u))) =
      (localReciprocityUnitCharacter (v.adicCompletion F) 2 χv a).toAdd :=
    hPair.trans hEval
  have hχ : finitePlaceDecompositionH1ToAdic F 2 v
      (h1OfCharacter (γ.comp (finitePlaceAbsoluteDecompositionInclusion F v))) = χv := by
    ext σ
    rfl
  unfold localRadicalValueAt
  rw [hχ]
  exact hEval'.trans (congrArg Multiplicative.toAdd hArtin)

end LocalValues

section Reciprocity

variable (F : Type) [Field F] [NumberField F]

theorem multiplicativeZModTwo_mul_self (x : Multiplicative (ZMod 2)) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  change x.toAdd + x.toAdd = 0
  generalize x.toAdd = y
  fin_cases y <;> decide

theorem multiplicativeZModTwo_inv (x : Multiplicative (ZMod 2)) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (multiplicativeZModTwo_mul_self x)

theorem multiplicativeZModTwo_toAdd_of_ne_one {x : Multiplicative (ZMod 2)} (hx : x ≠ 1) :
    x.toAdd = 1 := by
  have h : x.toAdd ≠ 0 := fun h => hx (Multiplicative.toAdd.injective (h.trans rfl))
  generalize x.toAdd = y at h ⊢
  fin_cases y
  · exact absurd rfl h
  · rfl

/-- The infinite part of an idele. -/
def infinitePart (x : IdeleGroup F) : IdeleGroup F := (x.1, 1)

/-- The infinite part is the product of its one-place components. -/
theorem infinitePart_eq_prod (x : IdeleGroup F) :
    infinitePart F x = ∏ w : InfinitePlace F,
      IdeleGroup.infinitePlaceIdele w (IdeleGroup.infiniteComponent w x) := by
  classical
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change IdeleGroup.infiniteComponent w (infinitePart F x) =
      IdeleGroup.infiniteComponent w (∏ w' : InfinitePlace F,
        IdeleGroup.infinitePlaceIdele w' (IdeleGroup.infiniteComponent w' x))
    rw [map_prod]
    rw [Finset.prod_eq_single w]
    · exact (IdeleGroup.infinitePlaceIdele_infiniteComponent_same w
        (IdeleGroup.infiniteComponent w x)).symm
    · intro w' _ hw'
      exact IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne w' w
        (IdeleGroup.infiniteComponent w' x) (Ne.symm hw')
    · intro h
      exact absurd (Finset.mem_univ w) h
  · rw [Prod.snd_prod]
    symm
    apply Finset.prod_eq_one
    intro w _
    rfl

/-- An idele character with values in `ℤ/2` on a real place: positive
elements are squares, negative ones are `−1` times squares. -/
theorem ideleCharacter_infinitePlaceIdele_real
    (ψ : IdeleGroup F →* Multiplicative (ZMod 2))
    (w : InfinitePlace F) (hw : w.IsReal) (t : w.Completionˣ) :
    ψ (IdeleGroup.infinitePlaceIdele w t) =
      if InfinitePlace.Completion.ringEquivRealOfIsReal hw (t : w.Completion) < 0 then
        ψ (IdeleGroup.infinitePlaceIdele w (-1)) else 1 := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let r : ℝ := e (t : w.Completion)
  have hr : r ≠ 0 := by
    intro h
    apply t.ne_zero
    apply e.injective
    rw [map_zero]
    exact h
  let q : ℝ := Real.sqrt |r|
  have hq : q * q = |r| := Real.mul_self_sqrt (abs_nonneg r)
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact hr (abs_eq_zero.mp hq.symm)
  let s : w.Completionˣ := Units.mk0 (e.symm q) (by
    intro h
    apply hq0
    have := congrArg e h
    rwa [e.apply_symm_apply, map_zero] at this)
  have hsq : ψ (IdeleGroup.infinitePlaceIdele w (s * s)) = 1 := by
    rw [map_mul, map_mul]
    exact multiplicativeZModTwo_mul_self _
  by_cases hneg : r < 0
  · rw [ite_eq_left hneg]
    have ht : t = -1 * (s * s) := by
      apply Units.ext
      apply e.injective
      change r = e ((-1 : w.Completionˣ) * (s * s) : w.Completionˣ)
      rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
      change r = e (-1) * (e (e.symm q) * e (e.symm q))
      rw [e.apply_symm_apply, hq, map_neg, map_one, abs_of_neg hneg]
      ring
    rw [ht, map_mul, map_mul, hsq, mul_one]
  · rw [ite_eq_right hneg]
    have hpos : 0 < r := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hr)
    have ht : t = s * s := by
      apply Units.ext
      apply e.injective
      change r = e ((s * s : w.Completionˣ) : w.Completion)
      rw [Units.val_mul, map_mul]
      change r = e (e.symm q) * e (e.symm q)
      rw [e.apply_symm_apply, hq, abs_of_pos hpos]
    rw [ht, hsq]

/-- The real coordinate of the principal idele at a real place is the real
embedding. -/
theorem ringEquivReal_infiniteComponent_principalIdele
    (w : InfinitePlace F) (hw : w.IsReal) (x : Fˣ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw
        (IdeleGroup.infiniteComponent w (IdeleGroup.principalIdele F x) : w.Completion) =
      InfinitePlace.embedding_of_isReal hw (x : F) := by
  rw [IdeleGroup.infiniteComponent_principalIdele,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw _

open scoped Classical in
/-- Global reciprocity for a principal unit: the finite local product over a
set containing the ramification is the value on the infinite part. -/
theorem finiteSupport_principal_unit
    (D : Finset (HeightOneSpectrum (𝓞 F)))
    (γ : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2))
    (hγ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ D →
      ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
        γ (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1)
    (u : (𝓞 F)ˣ) :
    (∏ v : ↥D, globalReciprocityIdeleCharacter F 2 γ
        (IdeleGroup.finitePlaceIdele v.1 (IdeleGroup.finiteComponent v.1
          (IdeleGroup.principalIdele F (RayClass.integralUnitToFieldUnit u))))) =
      globalReciprocityIdeleCharacter F 2 γ
        (infinitePart F (IdeleGroup.principalIdele F (RayClass.integralUnitToFieldUnit u))) := by
  let ψ := globalReciprocityIdeleCharacter F 2 γ
  let P : IdeleGroup F := IdeleGroup.principalIdele F (RayClass.integralUnitToFieldUnit u)
  let r : IdeleGroup F →ₜ* Multiplicative (ZMod 2) :=
    finiteSupportIdeleRestrictionCharacter F (2 : ℕ+) D ψ
  let δ : IdeleGroup F →ₜ* Multiplicative (ZMod 2) :=
    { toFun := fun x => ψ x / r x
      map_one' := by
        simp only [map_one]
        apply Multiplicative.toAdd.injective
        simp only [toAdd_div, toAdd_one, sub_self]
      map_mul' x y := by
        simp only [map_mul]
        exact mul_div_mul_comm _ _ _ _
      continuous_toFun := ψ.continuous.div' r.continuous }
  have div_one_target (z : Multiplicative (ZMod 2)) : z / 1 = z := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_div, toAdd_one]
    exact sub_zero _
  have hfinite : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ),
      a ∈ (v.adicCompletionIntegers F).units →
        δ (IdeleGroup.finitePlaceIdele v a) = 1 := by
    intro v a ha
    change ψ (IdeleGroup.finitePlaceIdele v a) /
      r (IdeleGroup.finitePlaceIdele v a) = 1
    rw [show r (IdeleGroup.finitePlaceIdele v a) =
      if v ∈ D then ψ (IdeleGroup.finitePlaceIdele v a) else 1 from
        finiteSupportIdeleRestrictionCharacter_finitePlace F (2 : ℕ+) D ψ v a]
    by_cases hv : v ∈ D
    · rw [ite_eq_left hv, div_self']
    · rw [ite_eq_right hv, div_one_target]
      apply globalReciprocityIdeleCharacter_integral_eq_one_of_inertia
        F (2 : ℕ+) γ v _ a ha
      intro σ
      exact hγ v hv σ
  have hIntegral : P ∈ IdeleGroup.integralAtFinitePlaces (K := F) :=
    IdeleGroup.principalRingUnit_mem_integralAtFinitePlaces (K := F) u
  let ufin : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).units :=
    fun v => ⟨P.2 v, hIntegral v⟩
  have hFiniteP : δ (integralFiniteIdeleContinuousHom F ufin) = 1 :=
    ideleCharacter_integralFinite_eq_one F (2 : ℕ+) δ hfinite ufin
  have hSplit : P = infinitePart F P * integralFiniteIdeleContinuousHom F ufin := by
    apply Prod.ext
    · exact (mul_one P.1).symm
    · exact (one_mul P.2).symm
  have hrInf : r (infinitePart F P) = 1 := by
    change (∏ v : ↥D, ψ (IdeleGroup.finitePlaceIdele v.1
      (IdeleGroup.finiteComponent v.1 (infinitePart F P)))) = 1
    apply Finset.prod_eq_one
    intro v _
    have h1 : IdeleGroup.finiteComponent v.1 (infinitePart F P) = 1 := by
      change (FiniteIdeleGroup.component v.1) (1 : FiniteIdeleGroup F) = 1
      exact map_one _
    rw [h1, map_one, map_one]
  have hψP : ψ P = 1 := globalReciprocityIdeleCharacter_principal F 2 γ _
  have hδP : δ P = ψ (infinitePart F P) := by
    have h1 : δ P = δ (infinitePart F P) * δ (integralFiniteIdeleContinuousHom F ufin) := by
      rw [← map_mul, ← hSplit]
    rw [h1, hFiniteP, mul_one]
    change ψ (infinitePart F P) / r (infinitePart F P) = _
    rw [hrInf, div_one_target]
  change ψ P / r P = ψ (infinitePart F P) at hδP
  rw [hψP, one_div] at hδP
  change r P = ψ (infinitePart F P)
  rw [← multiplicativeZModTwo_inv (r P)]
  exact hδP

/-- Over a totally real field: the sum over a finite set `D` containing the
ramification of `γ` of the local radical values of `γ` on the class of a unit
`u` is the number (mod 2) of real places where `u` is negative and `γ` is
nontrivial on the real Artin element. -/
theorem sum_localRadicalValueAt_unit [IsTotallyReal F]
    (D : Finset (HeightOneSpectrum (𝓞 F)))
    (γ : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2))
    (hγ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ D →
      ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
        γ (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1)
    (u : (𝓞 F)ˣ) :
    ∑ v : ↥D, localRadicalValueAt F v.1
        (h1OfCharacter (γ.comp (finitePlaceAbsoluteDecompositionInclusion F v.1)))
        (radicalUnit F u) =
      ∑ w : InfinitePlace F,
        if InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
            ((RayClass.integralUnitToFieldUnit u : Fˣ) : F) < 0 then
          (γ (absoluteInfinitePlaceArtinNegOne F w)).toAdd else 0 := by
  let ψ := globalReciprocityIdeleCharacter F 2 γ
  let P : IdeleGroup F := IdeleGroup.principalIdele F (RayClass.integralUnitToFieldUnit u)
  simp_rw [localRadicalValueAt_absoluteCharacter]
  rw [← toAdd_prod, finiteSupport_principal_unit F D γ hγ u]
  change (ψ (infinitePart F P)).toAdd = _
  rw [infinitePart_eq_prod, map_prod, toAdd_prod]
  apply Finset.sum_congr rfl
  intro w _
  have h := ideleCharacter_infinitePlaceIdele_real F ψ.toMonoidHom w (IsTotallyReal.isReal w)
    (IdeleGroup.infiniteComponent w P)
  change (ψ.toMonoidHom _).toAdd = _
  rw [h, ringEquivReal_infiniteComponent_principalIdele F w (IsTotallyReal.isReal w)]
  split_ifs with h
  · change (ψ (IdeleGroup.infinitePlaceIdele w (-1))).toAdd = _
    rw [globalReciprocityIdeleCharacter_infinite_neg_one F 2 γ w]
  · rfl

end Reciprocity

end UnitDistance.Sqrt241.Relation
