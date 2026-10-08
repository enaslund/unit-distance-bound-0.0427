module

public import UnitDistance.Sqrt241.GroupData.Retained
public import UnitDistance.Sqrt241.Cut.Basic

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The four D4 quotients factor through the retained model `Q_B`

For each of the D4 forms `24, 20, 17, 7` (index `i`), `D4 i = GroupModel (bilD4 i)` is the dihedral
group of order 8 written as `F₂² × F₂` with the bilinear law `bilD4 i`
(`x₀y₁` for rotation class `(1,1)`, `x₀y₁ + x₁y₁` for `(0,1)`); `φ₁ = (r₁, r₂) : F₂⁸ → F₂²` is its
Klein-four quotient (the rows of the form).

`lambdaHom i ℓ : Q_B →* D4 i` sends `(v, w)` to `(φ₁ v, λ(w) + q(v) + ℓ(v))` for any linear `ℓ`.
It is a homomorphism because

    λ(β_Q(v, v')) + β_D4(φ₁ v, φ₁ v') = q(v + v') - q(v) - q(v')

(`key`), where `λ` is a functional on the fifteen central coordinates of `Q_B` and `q` is a
quadratic form on `F₂⁸`. This is the statement that the D4 functional `ψ_i` of the form vanishes on
the 21 quadratic cut initials (papers/0.043171, Section 4, Lemma 2); here it is checked on the 64
pairs of basis vectors (`key_entries`, `decide +kernel`) and extended bilinearly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Wide

open ClassTwo GroupData

abbrev V4 : Type := Fin 2 → F

/-- First rows `r₁` of the forms (entry `k` ↔ radicand `α_k`): `√a = ∏ √α_k`, `k ∈ r₁`. -/
def rowA (i : Fin 4) : Fin 8 → F :=
  (![![0, 1, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0]] : Fin 4 → Fin 8 → F) i
/-- Second rows `r₂`. -/
def rowB (i : Fin 4) : Fin 8 → F :=
  (![![1, 0, 0, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 1, 0, 0, 0],
    ![1, 1, 0, 0, 0, 1, 0, 0]] : Fin 4 → Fin 8 → F) i

/-- The D4 law: `x₀ y₁`, plus `x₁ y₁` for the form `24` (rotation class `(0,1)`). -/
def bilFormula (i : Fin 4) (x y : V4) : F := x 0 * y 1 + (if i = 0 then x 1 * y 1 else 0)

/-- The D4 law as a bilinear map. -/
def bilD4 (i : Fin 4) : V4 →ₗ[F] V4 →ₗ[F] F :=
  LinearMap.mk₂ F (bilFormula i)
    (fun x x' y => by simp only [bilFormula, Pi.add_apply]; split_ifs <;> ring)
    (fun c x y => by simp only [bilFormula, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring)
    (fun x y y' => by simp only [bilFormula, Pi.add_apply]; split_ifs <;> ring)
    (fun c x y => by simp only [bilFormula, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring)

theorem bilD4_apply (i : Fin 4) (x y : V4) : bilD4 i x y = bilFormula i x y := rfl

/-- The dihedral group `D4 i`. -/
abbrev D4 (i : Fin 4) : Type := GroupModel (bilD4 i)

instance (i : Fin 4) : TopologicalSpace (D4 i) := ⊥
instance (i : Fin 4) : DiscreteTopology (D4 i) := ⟨rfl⟩
instance (i : Fin 4) : IsTopologicalGroup (D4 i) := inferInstance
instance (i : Fin 4) : T2Space (D4 i) := inferInstance
instance (i : Fin 4) : CompactSpace (D4 i) := inferInstance
instance (i : Fin 4) : TotallyDisconnectedSpace (D4 i) := inferInstance

theorem d4_isTwoGroup (i : Fin 4) : IsPGroup 2 (D4 i) := GroupModel.isTwoGroup (bilD4 i)

open ProCGroups ProCGroups.ProC in
theorem d4_hasPGroupOpenNormalBasis (i : Fin 4) : HasPGroupOpenNormalBasis 2 (D4 i) := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance, (d4_isTwoGroup i).of_surjective (QuotientGroup.mk' (U : Subgroup (D4 i)))
    (QuotientGroup.mk'_surjective (U : Subgroup (D4 i)))⟩

/-- The Klein-four quotient `φ₁ = (r₁, r₂) : F₂⁸ → F₂²`. -/
def phi1 (i : Fin 4) : (Fin 8 → F) →ₗ[F] V4 where
  toFun v := ![∑ k, rowA i k * v k, ∑ k, rowB i k * v k]
  map_add' v w := by
    funext c
    fin_cases c <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    funext c
    fin_cases c <;> simp [Finset.mul_sum, mul_left_comm]

theorem phi1_apply_zero (i : Fin 4) (v : Fin 8 → F) : phi1 i v 0 = ∑ k, rowA i k * v k := rfl
theorem phi1_apply_one (i : Fin 4) (v : Fin 8 → F) : phi1 i v 1 = ∑ k, rowB i k * v k := rfl

/-- The functional `λ` on the central coordinates of `Q_B`. -/
def lamMask : Fin 4 → ℕ := ![25333, 8804, 16580, 18592]

def lam (i : Fin 4) : Retained.W →ₗ[F] F := maskFunctional 15 (lamMask i)

/-- Rows of the symmetric matrix `E = λ ∘ β_Q + β_D4 ∘ (φ₁ × φ₁)` (zero diagonal). -/
def dMask : Fin 4 → Fin 8 → ℕ :=
  ![![0b00011000, 0b00011000, 0, 0b00000011, 0b00000011, 0, 0, 0],
    ![0, 0b10001000, 0, 0b00000010, 0b10000000, 0b10000000, 0, 0b00110010],
    ![0, 0b00010000, 0, 0, 0b00000010, 0, 0, 0],
    ![0, 0, 0, 0, 0b00100000, 0b00010000, 0, 0]]

def dmat (i : Fin 4) (j k : Fin 8) : F := bits 8 (dMask i j) k

/-- The coefficient of `v_j v_k` (`j < k`) in the quadratic form `q`. -/
def dcoef (i : Fin 4) (j k : Fin 8) : F := if j < k then dmat i j k else 0

/-- The quadratic form `q(v) = ∑_{j<k} E_jk v_j v_k`. -/
def qq (i : Fin 4) (v : Fin 8 → F) : F := ∑ j, ∑ k, dcoef i j k * (v j * v k)

/-- Its polar form. -/
def polar (i : Fin 4) : (Fin 8 → F) →ₗ[F] (Fin 8 → F) →ₗ[F] F :=
  LinearMap.mk₂ F (fun v w => ∑ j, ∑ k, dcoef i j k * (v j * w k + w j * v k))
    (fun v v' w => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring)
    (fun c v w => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring)
    (fun v w w' => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring)
    (fun c v w => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring)

theorem polar_apply (i : Fin 4) (v w : Fin 8 → F) :
    polar i v w = ∑ j, ∑ k, dcoef i j k * (v j * w k + w j * v k) := rfl

theorem qq_add (i : Fin 4) (v w : Fin 8 → F) : qq i (v + w) = qq i v + qq i w + polar i v w := by
  simp only [qq, polar_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem qq_zero (i : Fin 4) : qq i 0 = 0 := by simp [qq]

/-- The bilinear map `λ ∘ β_Q + β_D4 ∘ (φ₁ × φ₁)`. -/
def lhsBil (i : Fin 4) : (Fin 8 → F) →ₗ[F] (Fin 8 → F) →ₗ[F] F :=
  Retained.cocycle.compr₂ (lam i) + (bilD4 i).compl₁₂ (phi1 i) (phi1 i)

theorem lhsBil_apply (i : Fin 4) (v w : Fin 8 → F) :
    lhsBil i v w = lam i (Retained.cocycle v w) + bilD4 i (phi1 i v) (phi1 i w) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The 64 basis values of `λ ∘ β_Q + β_D4 ∘ (φ₁ × φ₁)` are those of the polar form of `q`. -/
theorem key_entries : ∀ (i : Fin 4) (a b : Fin 8),
    lhsBil i (Pi.single a 1) (Pi.single b 1) = polar i (Pi.single a 1) (Pi.single b 1) := by
  decide +kernel

theorem lhsBil_eq_polar (i : Fin 4) : lhsBil i = polar i := by
  apply linearMap_ext_single
  intro a
  apply linearMap_ext_single
  intro b
  exact key_entries i a b

/-- **Key identity.** -/
theorem key (i : Fin 4) (v w : Fin 8 → F) :
    lam i (Retained.cocycle v w) + qq i (v + w) = qq i v + qq i w + bilD4 i (phi1 i v) (phi1 i w) := by
  have h := congrArg (fun B : (Fin 8 → F) →ₗ[F] (Fin 8 → F) →ₗ[F] F => B v w) (lhsBil_eq_polar i)
  simp only [lhsBil_apply] at h
  rw [qq_add, ← h]
  have h2 : ∀ a : F, a + a = 0 := by decide
  have e := h2 (lam i (Retained.cocycle v w))
  linear_combination e

/-- `Λ_i : Q_B →* D4 i`, `(v, w) ↦ (φ₁ v, λ(w) + q(v) + ℓ(v))`. -/
def lambdaHom (i : Fin 4) (ell : (Fin 8 → F) →ₗ[F] F) : Retained.Q →* D4 i where
  toFun g := ⟨phi1 i g.base, lam i g.central + qq i g.base + ell g.base⟩
  map_one' := by
    apply GroupModel.ext
    · exact map_zero (phi1 i)
    · change lam i 0 + qq i 0 + ell 0 = 0
      rw [map_zero, qq_zero, map_zero, add_zero, add_zero]
  map_mul' g h := by
    apply GroupModel.ext
    · exact map_add (phi1 i) g.base h.base
    · change lam i (g.central + h.central + Retained.cocycle g.base h.base) +
          qq i (g.base + h.base) + ell (g.base + h.base) =
        (lam i g.central + qq i g.base + ell g.base) + (lam i h.central + qq i h.base + ell h.base) +
          bilD4 i (phi1 i g.base) (phi1 i h.base)
      rw [map_add, map_add, map_add]
      have hk := key i g.base h.base
      linear_combination hk

theorem lambdaHom_apply (i : Fin 4) (ell : (Fin 8 → F) →ₗ[F] F) (g : Retained.Q) :
    lambdaHom i ell g = ⟨phi1 i g.base, lam i g.central + qq i g.base + ell g.base⟩ := rfl

theorem qq_single (i : Fin 4) (a : Fin 8) : qq i (Pi.single a 1) = 0 := by
  simp only [qq, Pi.single_apply]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases hj : j = a <;> by_cases hk : k = a
  · subst hj
    subst hk
    simp [dcoef]
  · simp [hk]
  · simp [hj]
  · simp [hj]

/-- The image of a free generator `(e_a, 0)`. -/
theorem lambdaHom_generator (i : Fin 4) (ell : (Fin 8 → F) →ₗ[F] F) (a : Fin 8) :
    lambdaHom i ell ⟨Pi.single a 1, 0⟩ = ⟨phi1 i (Pi.single a 1), ell (Pi.single a 1)⟩ := by
  rw [lambdaHom_apply]
  congr 1
  change lam i 0 + qq i (Pi.single a 1) + ell (Pi.single a 1) = ell (Pi.single a 1)
  rw [map_zero, qq_single, zero_add, zero_add]

end UnitDistance.Sqrt241.Wide
