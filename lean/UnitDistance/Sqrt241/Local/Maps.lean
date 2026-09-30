module

public import UnitDistance.Sqrt241.Tower.Bridge
public import UnitDistance.Sqrt241.ProP.AbsoluteProPRestriction
public import UnitDistance.Sqrt241.Local.DyadicSigns
public import UnitDistance.Sqrt241.Local.Conjugation
public import UnitDistance.AbsoluteLocalCompactness
public import UnitDistance.PadicTwoQuadraticRelation

@[expose] public section
set_option backward.privateInPublic true

/-!
# Local maps into `Ĝ = Gal(Ω/ℚ)` and `G_B`, and their normalization

`toGhat` restricts absolute automorphisms of the closure to `Ω`
(`ProP.absoluteToNormal`). The chosen decomposition group above a rational prime `p`
maps continuously into `Ĝ` (`decompositionMap p`), and into `G_B` when `241` is a
`p`-adic square (`decompositionMapB`; its elements fix `B`, `Place.lean`).

**Normalization.** The chosen place lies above one of the two primes of `B` over
`p` (index `P₀ : Fin 2`, known only through the Base tables). The normalized local
map at the prime `P` is `decompositionMapB` followed by conjugation with
`frame P₀ P` (`1` if `P = P₀`, else `σ̂ = sigmaHat`): conjugating by a lift of `σ`
moves the chosen place to the other prime of `B`.

**Labels.** `HasLabelHat g v` says that `g ∈ Ĝ` is the restriction of an absolute
automorphism with genus label `v` (`Conjugation.lean`). Labels multiply, and
conjugation by `σ̂` acts by `sigmaMatrix` (`HasLabelHat.conj_sigmaHat`).

**Dyadic map.** `dyadicLocal P : PadicTwoMaximalProTwo.Group →ₜ* G_B` is the
normalized map from the maximal pro-2 quotient of `Gal(ℚ̄₂/ℚ₂)` (the ℚ package's
`PadicTwoGlobalMap.toGlobal` pattern with target `G_B`); its genus labels are
`dyadicSignVector P` of the three local signs (`dyadicLocal_hasLabel`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField CanonicalGenus Base UnitDistance.PrimeCompletion Multiquadratic Tower
open ProCGroups ProCGroups.ProC

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ## Restriction to `Ω` -/

/-- Restriction of absolute automorphisms to `Ω`. -/
def toGhat : Gal(Closure/ℚ) →ₜ* Ghat :=
  ProP.absoluteToNormal ℚ Omega inferInstance

theorem toGhat_apply (σ : Gal(Closure/ℚ)) (x : Omega) :
    (toGhat σ x : Closure) = σ (x : Closure) :=
  ProP.absoluteToNormal_apply ℚ Omega inferInstance σ x

theorem toGhat_surjective : Function.Surjective toGhat :=
  ProP.absoluteToNormal_surjective ℚ Omega inferInstance

theorem toGhat_mem_GB_iff (σ : Gal(Closure/ℚ)) :
    toGhat σ ∈ GB ↔ σ baseRoot = baseRoot := by
  rw [mem_GB_iff]
  constructor
  · intro h
    have h' := congrArg (fun y : Omega => (y : Closure)) h
    simpa only [toGhat_apply, coe_rootOmega] using h'
  · intro h
    apply Subtype.ext
    rw [toGhat_apply]
    exact h

theorem toGhat_not_mem_GB_iff (σ : Gal(Closure/ℚ)) :
    toGhat σ ∉ GB ↔ σ baseRoot = -baseRoot := by
  rw [not_mem_GB_iff]
  constructor
  · intro h
    have h' := congrArg (fun y : Omega => (y : Closure)) h
    simpa only [toGhat_apply, coe_rootOmega, IntermediateField.coe_neg] using h'
  · intro h
    apply Subtype.ext
    rw [toGhat_apply]
    simpa using h

/-- A lift of `σ̂` to the absolute Galois group; it moves `√241`. -/
def sigmaLift : Gal(Closure/ℚ) := Function.surjInv toGhat_surjective sigmaHat

theorem toGhat_sigmaLift : toGhat sigmaLift = sigmaHat :=
  Function.surjInv_eq toGhat_surjective sigmaHat

theorem sigmaLift_baseRoot : sigmaLift baseRoot = -baseRoot := by
  rw [← toGhat_not_mem_GB_iff, toGhat_sigmaLift]
  exact sigmaHat_not_mem

/-! ## Labels in `Ĝ` -/

/-- `g ∈ Ĝ` is the restriction of an absolute automorphism with genus label `v`. -/
def HasLabelHat (g : Ghat) (v : Fin 8 → ZMod 2) : Prop :=
  ∃ σ : Gal(Closure/ℚ), toGhat σ = g ∧ HasLabel σ v

theorem HasLabelHat.mul {g h : Ghat} {v w : Fin 8 → ZMod 2} (hg : HasLabelHat g v)
    (hh : HasLabelHat h w) : HasLabelHat (g * h) (v + w) := by
  obtain ⟨σ, rfl, hσ⟩ := hg
  obtain ⟨τ, rfl, hτ⟩ := hh
  exact ⟨σ * τ, map_mul _ _ _, hσ.mul hτ⟩

theorem HasLabelHat.inv {g : Ghat} {v : Fin 8 → ZMod 2} (hg : HasLabelHat g v) :
    HasLabelHat g⁻¹ v := by
  obtain ⟨σ, rfl, hσ⟩ := hg
  exact ⟨σ⁻¹, map_inv _ _, hσ.inv⟩

theorem HasLabelHat.pow {g : Ghat} {v : Fin 8 → ZMod 2} (hg : HasLabelHat g v) (n : ℕ) :
    HasLabelHat (g ^ n) (n • v) := by
  obtain ⟨σ, rfl, hσ⟩ := hg
  exact ⟨σ ^ n, map_pow _ _ _, hσ.pow n⟩

theorem hasLabelHat_one : HasLabelHat 1 0 := ⟨1, map_one _, hasLabel_one⟩

/-- **Conjugation rule in `Ĝ`.** -/
theorem HasLabelHat.conj_sigmaHat {g : Ghat} {v : Fin 8 → ZMod 2} (hg : HasLabelHat g v) :
    HasLabelHat (sigmaHat * g * sigmaHat⁻¹) (sigmaMatrix v) := by
  obtain ⟨σ, rfl, hσ⟩ := hg
  refine ⟨sigmaLift * σ * sigmaLift⁻¹, ?_, hasLabel_conj sigmaLift_baseRoot hσ⟩
  rw [map_mul, map_mul, map_inv, toGhat_sigmaLift]

/-- Labels are unique once the genus field lies in `Ω` (any lift has the same action). -/
theorem HasLabelHat.unique (hE : CanonicalGenus.field ≤ Omega) {g : Ghat}
    {v w : Fin 8 → ZMod 2} (hv : HasLabelHat g v) (hw : HasLabelHat g w) : v = w := by
  obtain ⟨σ, rfl, hσ⟩ := hv
  obtain ⟨τ, hτg, hτ⟩ := hw
  have hτ' : HasLabel σ w := by
    intro k
    have hk : genusRoot k ∈ Omega := hE (genusRoot_mem k)
    have h := congrArg (fun g : Ghat => ((g ⟨genusRoot k, hk⟩ : Omega) : Closure)) hτg
    simp only [toGhat_apply] at h
    rw [← h]
    exact hτ k
  exact hσ.unique hτ'

/-- With the genus field in `Ω`, a label is the action on the genus roots. -/
theorem HasLabelHat.apply_genusRoot (hE : CanonicalGenus.field ≤ Omega) {g : Ghat}
    {v : Fin 8 → ZMod 2} (hg : HasLabelHat g v) (k : Fin 8) :
    ((g ⟨genusRoot k, hE (genusRoot_mem k)⟩ : Omega) : Closure) = binarySign (v k) * genusRoot k := by
  obtain ⟨σ, rfl, hσ⟩ := hg
  rw [toGhat_apply]
  exact hσ k

/-! ## Decomposition maps -/

/-- The chosen decomposition group above `p`, mapped into `Ĝ`. -/
def decompositionMap (p : Nat.Primes) : AbsoluteDecomposition p →ₜ* Ghat :=
  toGhat.comp ⟨(AbsoluteDecomposition p).subtype, continuous_subtype_val⟩

theorem decompositionMap_apply (p : Nat.Primes) (d : AbsoluteDecomposition p) :
    decompositionMap p d = toGhat d.val := rfl

theorem decompositionMap_mem_GB (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val]))
    (d : AbsoluteDecomposition p) : decompositionMap p d ∈ GB :=
  (toGhat_mem_GB_iff _).mpr (decomposition_fixes_baseRoot p hsq d)

/-- The chosen decomposition group above a split prime, mapped into `G_B`. -/
def decompositionMapB (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val])) :
    AbsoluteDecomposition p →ₜ* GB where
  toFun d := ⟨decompositionMap p d, decompositionMap_mem_GB p hsq d⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  continuous_toFun := (decompositionMap p).continuous.subtype_mk _

@[simp] theorem coe_decompositionMapB (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val]))
    (d : AbsoluteDecomposition p) : (decompositionMapB p hsq d : Ghat) = decompositionMap p d :=
  rfl

/-! ## Conjugation and frames -/

/-- Conjugation by an element of `Ĝ`, as a continuous endomorphism of `G_B`. -/
def conjGB (g : Ghat) : GB →ₜ* GB where
  toFun h := ⟨g * h * g⁻¹, GB_normal.conj_mem _ h.2 g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

@[simp] theorem coe_conjGB (g : Ghat) (h : GB) : (conjGB g h : Ghat) = g * h * g⁻¹ := rfl

theorem conjGB_one : conjGB 1 = ContinuousMonoidHom.id GB := by
  ext h
  simp

/-- The normalizing element: `1` if the chosen place lies over `P`, else `σ̂`. -/
def frame (P₀ P : Fin 2) : Ghat := if P = P₀ then 1 else sigmaHat

theorem frame_self (P : Fin 2) : frame P P = 1 := by simp [frame]

theorem frame_ne {P₀ P : Fin 2} (h : P ≠ P₀) : frame P₀ P = sigmaHat := by simp [frame, h]

/-- The normalized local map at the prime `P` of `B` above `p`, when the chosen place
lies above the prime `P₀`. -/
def localMapB (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val])) (P₀ P : Fin 2) :
    AbsoluteDecomposition p →ₜ* GB :=
  (conjGB (frame P₀ P)).comp (decompositionMapB p hsq)

theorem coe_localMapB (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val])) (P₀ P : Fin 2)
    (d : AbsoluteDecomposition p) :
    (localMapB p hsq P₀ P d : Ghat) = frame P₀ P * decompositionMap p d * (frame P₀ P)⁻¹ :=
  rfl

/-- Labels at the normalized map: the chosen place's label, or its `sigmaMatrix` image. -/
theorem localMapB_hasLabel (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val])) (P₀ P : Fin 2)
    (d : AbsoluteDecomposition p) {v : Fin 8 → ZMod 2} (hd : HasLabel d.val v) :
    HasLabelHat (localMapB p hsq P₀ P d) (if P = P₀ then v else sigmaMatrix v) := by
  have h0 : HasLabelHat (decompositionMap p d) v := ⟨d.val, rfl, hd⟩
  rw [coe_localMapB]
  by_cases hP : P = P₀
  · simp only [hP, ↓reduceIte, frame_self, one_mul, inv_one, mul_one]
    exact h0
  · simp only [hP, ↓reduceIte, frame_ne hP]
    exact h0.conj_sigmaHat

/-! ## The dyadic local map -/

/-- The ℚ package's local-to-global comparison at `2`, as a continuous homomorphism into
the chosen decomposition group. -/
def dyadicDecomposition : PadicTwoMaximalProTwo.AbsoluteGroup →ₜ* AbsoluteDecomposition prime2 :=
  (⟨(decompositionEquiv prime2).symm.toMulEquiv.toMonoidHom,
      (decompositionEquiv prime2).symm.continuous⟩ :
    Gal(PadicTwoGlobalMap.LocalClosure/PadicTwoGlobalMap.Base) →ₜ* AbsoluteDecomposition prime2).comp
    PadicTwoGlobalMap.absoluteHom

theorem dyadicDecomposition_apply (σ : PadicTwoMaximalProTwo.AbsoluteGroup) :
    dyadicDecomposition σ = PadicTwoGlobalMap.decomposition σ := rfl

/-- The unnormalized absolute dyadic map into `G_B` (at the chosen place). -/
def dyadicAbsolute : PadicTwoMaximalProTwo.AbsoluteGroup →ₜ* GB :=
  (decompositionMapB prime2 isSquare_241_two).comp dyadicDecomposition

/-- **The normalized dyadic local map** at `𝔭₁` (`P = 0`) and `𝔭₂` (`P = 1`). -/
def dyadicLocal (P : Fin 2) : PadicTwoMaximalProTwo.Group →ₜ* GB :=
  lift_proCResidualCoreQuotient (FiniteGroupClass.pGroup_hereditary 2)
    ((conjGB (frame dyadicPlace P)).comp dyadicAbsolute) GB_hasPGroupOpenNormalBasis

@[simp] theorem dyadicLocal_projection (P : Fin 2) (σ : PadicTwoMaximalProTwo.AbsoluteGroup) :
    dyadicLocal P (PadicTwoMaximalProTwo.projection σ) =
      conjGB (frame dyadicPlace P) (dyadicAbsolute σ) := rfl

theorem fin2_one_sub_of_ne {P Q : Fin 2} (h : P ≠ Q) : 1 - Q = P := by
  revert h
  revert P Q
  decide

theorem dyadicSignVector_sigmaMatrix (P : Fin 2) (v : Fin 3 → ZMod 2) :
    sigmaMatrix (dyadicSignVector P v) = dyadicSignVector (1 - P) v := by
  have h : ∀ P : Fin 2, ∀ v : Fin 3 → ZMod 2,
      sigmaMatrix (dyadicSignVector P v) = dyadicSignVector (1 - P) v := by decide +kernel
  exact h P v

/-- **Dyadic labels.** Every element of the local pro-2 group maps to an element of
`G_B` with genus label `dyadicSignVector P` of its three local signs. -/
theorem dyadicLocal_hasLabel (P : Fin 2) (g : PadicTwoMaximalProTwo.Group) :
    HasLabelHat (dyadicLocal P g) (dyadicSignVector P (PadicTwoMaximalProTwo.signs g).toAdd) := by
  obtain ⟨σ, rfl⟩ := PadicTwoMaximalProTwo.projection_surjective g
  rw [dyadicLocal_projection, PadicTwoMaximalProTwo.signs_projection]
  have hd : HasLabel (PadicTwoGlobalMap.decomposition σ).val
      (dyadicSignVector dyadicPlace (PadicTwoMaximalProTwo.absoluteSigns σ).toAdd) :=
    decomposition_genusRoot σ
  have h := localMapB_hasLabel prime2 isSquare_241_two dyadicPlace P
    (PadicTwoGlobalMap.decomposition σ) hd
  change HasLabelHat ((localMapB prime2 isSquare_241_two dyadicPlace P
    (dyadicDecomposition σ) : Ghat)) _
  rw [dyadicDecomposition_apply]
  by_cases hP : P = dyadicPlace
  · have e : ∀ a b : Fin 8 → ZMod 2, (if P = dyadicPlace then a else b) = a :=
      fun a b => by simp [hP]
    rw [e] at h
    rw [show dyadicSignVector P (PadicTwoMaximalProTwo.absoluteSigns σ).toAdd =
      dyadicSignVector dyadicPlace (PadicTwoMaximalProTwo.absoluteSigns σ).toAdd by rw [hP]]
    exact h
  · have e : ∀ a b : Fin 8 → ZMod 2, (if P = dyadicPlace then a else b) = b :=
      fun a b => by simp [hP]
    rw [e, dyadicSignVector_sigmaMatrix, fin2_one_sub_of_ne hP] at h
    exact h

/-- The labels of the three local generators `(a, b, c)` of `PadicTwoQuadraticRelation`. -/
theorem dyadicLocal_generator_hasLabel (P : Fin 2) (i : Fin 3) :
    HasLabelHat (dyadicLocal P (PadicTwoQuadraticRelation.generator i))
      (RetainedQuadratic.binaryVector 8 (dyadicMasks P i)) := by
  have h := dyadicLocal_hasLabel P (PadicTwoQuadraticRelation.generator i)
  rwa [PadicTwoQuadraticRelation.generator_signs, dyadicSignVector_genusBasis] at h

end UnitDistance.Sqrt241.Local
