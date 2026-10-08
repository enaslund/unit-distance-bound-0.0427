import sys
FORMS = [  # index, orbit, A roots, B roots, M, (sign, a2, a3)
 (0, 24, [1,3,4,5,6,7], [0,3,4], 660451885056, (1, 25, 9)),
 (1, 20, [1,4,5], [0,3,7], 68719476736, (1, 36, 0)),
 (2, 17, [1,5,6], [0,4], -768, (-1, 8, 1)),
 (3, 7, [4,6], [0,1,5], 768, (1, 8, 1)),
]
CV = "Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one"
def prodO(ks): return " * ".join(f"gO {k}" for k in ks)
out = []
for i, o, A, Bk, M, (sg, a2, a3) in FORMS:
    out.append(f'''
/-! ### Form {o} (index {i}) -/

theorem rootA_mem_genusB_{i} : rootA {i} ∈ genusB := by
  simp only [rootA, {CV}]
  repeat' apply mul_mem
  all_goals exact genusRoot_mem_genusB _

theorem rootB_mem_genusB_{i} : rootB {i} ∈ genusB := by
  simp only [rootB, {CV}]
  repeat' apply mul_mem
  all_goals exact genusRoot_mem_genusB _

theorem sigma_rootA_{i} (σ : Closure ≃ₐ[B] Closure) :
    σ (rootA {i}) = rootA {i} ∨ σ (rootA {i}) = -rootA {i} := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, rootA_sq_{i}]
  simp [map_sub, map_add, map_mul, map_div₀, map_neg, map_ofNat, sigma_baseRoot_B σ]

theorem sigma_rootB_{i} (σ : Closure ≃ₐ[B] Closure) :
    σ (rootB {i}) = rootB {i} ∨ σ (rootB {i}) = -rootB {i} := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, rootB_sq_{i}]
  simp [map_sub, map_add, map_mul, map_div₀, map_neg, map_ofNat, sigma_baseRoot_B σ]

/-- `β_{o}` as an algebraic integer of the genus field. -/
def betaO_{i} : 𝓞 genusB := beta{o} sO (rootAO {i}) (rootBO {i})

theorem oHom_betaO_{i} : oHom betaO_{i} = wideRadicand {i} := by
  rw [betaO_{i}, beta{o}_map, oHom_sO, oHom_rootAO, oHom_rootBO, wideRadicand_{i}]

/-- The cofactor of the norm of `β_{o}`. -/
def cofO_{i} : 𝓞 genusB :=
  normConj{o} sO (rootAO {i}) (rootBO {i}) *
    algebraMap (𝓞 B) (𝓞 genusB) (mk normBarMk{o}.1 normBarMk{o}.2)

theorem betaO_mul_cofO_{i} : betaO_{i} * cofO_{i} = (({M} : ℤ) : 𝓞 genusB) := by
  apply oHom_injective
  rw [map_mul, oHom_betaO_{i}, cofO_{i}, map_mul, normConj{o}_map, oHom_sO, oHom_rootAO, oHom_rootBO,
    oHom_algebraMap_mk, map_intCast, wideRadicand_{i}]
  have h := beta{o}_mul_normCofactor baseRoot (rootA {i}) (rootB {i}) baseRoot_sq rootA_sq_{i} rootB_sq_{i}
  rw [normCofactor{o}, ← normBar{o}_eq] at h
  simp only [normBarMk{o}] at h ⊢
  exact_mod_cast h

theorem hm30_{i} : ∀ P : Ideal ℤ, P.IsPrime → ({M} : ℤ) ∈ P → (30 : ℤ) ∈ P := by
  intro P hP hM
  apply thirty_mem_of_two_three P {a2} {a3}
  have he : ({M} : ℤ) = {"-" if sg < 0 else ""}(2 ^ {a2} * 3 ^ {a3}) := by norm_num
  rw [he] at hM
  {"simpa using neg_mem hM" if sg < 0 else "exact hM"}

theorem hconj_{i} (σ : Closure ≃ₐ[B] Closure) :
    ∃ u ∈ genusB, σ ((betaO_{i} : genusB) : Closure) = u ^ 2 * ((betaO_{i} : genusB) : Closure) := by
  have hb : ((betaO_{i} : genusB) : Closure) = beta{o} baseRoot (rootA {i}) (rootB {i}) := by
    rw [← wideRadicand_{i}, ← oHom_betaO_{i}]
    rfl
  rw [hb, show σ (beta{o} baseRoot (rootA {i}) (rootB {i})) =
      beta{o} (σ baseRoot) (σ (rootA {i})) (σ (rootB {i})) from beta{o}_map σ.toRingHom _ _ _,
    sigma_baseRoot_B σ]
  have hs := baseRoot_mem_genusB
  have ha := rootA_mem_genusB_{i}
  have hb' := rootB_mem_genusB_{i}
  rcases sigma_rootA_{i} σ with hx | hx <;> rcases sigma_rootB_{i} σ with hy | hy <;> rw [hx, hy]
  · exact ⟨1, one_mem _, by ring⟩
  · refine ⟨u{o}_01 baseRoot (rootA {i}) (rootB {i}), ?_,
      beta{o}_sigma_01 _ _ _ baseRoot_sq rootA_sq_{i} rootB_sq_{i}⟩
    have hmem : genusB.val (u{o}_01 ⟨_, hs⟩ ⟨_, ha⟩ ⟨_, hb'⟩) ∈ genusB := SetLike.coe_mem _
    rwa [show genusB.val (u{o}_01 ⟨_, hs⟩ ⟨_, ha⟩ ⟨_, hb'⟩) =
      u{o}_01 baseRoot (rootA {i}) (rootB {i}) from u{o}_01_map genusB.val.toRingHom _ _ _] at hmem
  · refine ⟨u{o}_10 baseRoot (rootA {i}) (rootB {i}), ?_,
      beta{o}_sigma_10 _ _ _ baseRoot_sq rootA_sq_{i} rootB_sq_{i}⟩
    have hmem : genusB.val (u{o}_10 ⟨_, hs⟩ ⟨_, ha⟩ ⟨_, hb'⟩) ∈ genusB := SetLike.coe_mem _
    rwa [show genusB.val (u{o}_10 ⟨_, hs⟩ ⟨_, ha⟩ ⟨_, hb'⟩) =
      u{o}_10 baseRoot (rootA {i}) (rootB {i}) from u{o}_10_map genusB.val.toRingHom _ _ _] at hmem
  · refine ⟨u{o}_11 baseRoot (rootA {i}) (rootB {i}), ?_,
      beta{o}_sigma_11 _ _ _ baseRoot_sq rootA_sq_{i} rootB_sq_{i}⟩
    have hmem : genusB.val (u{o}_11 ⟨_, hs⟩ ⟨_, ha⟩ ⟨_, hb'⟩) ∈ genusB := SetLike.coe_mem _
    rwa [show genusB.val (u{o}_11 ⟨_, hs⟩ ⟨_, ha⟩ ⟨_, hb'⟩) =
      u{o}_11 baseRoot (rootA {i}) (rootB {i}) from u{o}_11_map genusB.val.toRingHom _ _ _] at hmem

/-- **`√β_{o} ∈ Ω`.** -/
theorem wideRoot_mem_OmegaBcl_{i} : wideRoot {i} ∈ OmegaBcl := by
  have h := squareRoot_mem_OmegaBcl genusB admissible_genusB betaO_{i} cofO_{i} ({M})
    betaO_mul_cofO_{i} hm30_{i} hconj_{i}
  have hb : ((betaO_{i} : genusB) : Closure) = wideRadicand {i} := oHom_betaO_{i}
  rwa [hb] at h
''')
hdr = '''module

public import UnitDistance.Sqrt241.Wide.Basic
public import UnitDistance.Sqrt241.Wide.Kummer

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# The four D4 radicands of `E_W` have square roots in `Ω`

Generated by `scripts/sqrt241/generate_wide_omega.py` — do not edit by hand.

For each form, `β_i = wideRadicand i` is an algebraic integer of the genus field `genusB`
(`betaO_i`), an `S`-unit (`β_i · cofO_i = m_i` with `m_i = ±2^a 3^b`), and every
`B`-automorphism `σ` of the closure satisfies `σ(β_i) = u² β_i` with `u ∈ genusB`
(`Wide/Identities.lean`). By `squareRoot_mem_OmegaBcl`, `√β_i ∈ Ω`; hence `E_W ≤ Ω`.
-/

open scoped NumberField
open NumberField

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Wide

open Tower Base CanonicalGenus CanonicalWide IntermediateField

theorem sigma_baseRoot_B (σ : Closure ≃ₐ[B] Closure) : σ baseRoot = baseRoot := by
  have h := σ.commutes sqrt241
  rwa [IntermediateField.algebraMap_apply, coe_sqrt241] at h

/-- A prime ideal of `ℤ` containing `2^a 3^b` contains `30`. -/
theorem thirty_mem_of_two_three (P : Ideal ℤ) [hP : P.IsPrime] (a b : ℕ)
    (h : (2 : ℤ) ^ a * 3 ^ b ∈ P) : (30 : ℤ) ∈ P := by
  rcases hP.mem_or_mem h with h2 | h3
  · have := hP.mem_of_pow_mem a h2
    have h30 : (30 : ℤ) = 15 * 2 := by norm_num
    rw [h30]
    exact P.mul_mem_left 15 this
  · have := hP.mem_of_pow_mem b h3
    have h30 : (30 : ℤ) = 10 * 3 := by norm_num
    rw [h30]
    exact P.mul_mem_left 10 this

/-! ### Integral generators of the genus field -/

/-- `√α_k` as an algebraic integer of `genusB`. -/
def gO (k : Fin 8) : 𝓞 genusB :=
  ⟨⟨genusRoot k, genusRoot_mem_genusB k⟩, by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    have h : (⟨genusRoot k, genusRoot_mem_genusB k⟩ : genusB) ^ 2 =
        algebraMap B genusB ((alpha k : 𝓞 B) : B) := by
      apply Subtype.ext
      change genusRoot k ^ 2 = _
      rw [genusRoot_sq_alpha]
      rfl
    rw [h]
    exact ((alpha k).2).map (IsScalarTower.toAlgHom ℤ B genusB)⟩

/-- `√241` as an algebraic integer of `genusB`. -/
def sO : 𝓞 genusB := algebraMap (𝓞 B) (𝓞 genusB) sqrt241Int

/-- The coercion `𝓞 genusB → Closure` as a ring homomorphism. -/
def oHom : 𝓞 genusB →+* Closure :=
  (IntermediateField.val genusB).toRingHom.comp (algebraMap (𝓞 genusB) genusB)

theorem oHom_apply (x : 𝓞 genusB) : oHom x = ((x : genusB) : Closure) := rfl

theorem oHom_injective : Function.Injective oHom :=
  Subtype.val_injective.comp RingOfIntegers.coe_injective

@[simp] theorem oHom_gO (k : Fin 8) : oHom (gO k) = genusRoot k := rfl

theorem oHom_algebraMap (b : 𝓞 B) :
    oHom (algebraMap (𝓞 B) (𝓞 genusB) b) = (((b : 𝓞 B) : B) : Closure) := rfl

@[simp] theorem oHom_sO : oHom sO = baseRoot := by
  rw [sO, oHom_algebraMap, coe_sqrt241Int, coe_sqrt241]

theorem oHom_algebraMap_mk (m n : ℤ) :
    oHom (algebraMap (𝓞 B) (𝓞 genusB) (mk m n)) = (m : Closure) + (n : Closure) * ((1 + baseRoot) / 2) := by
  unfold Base.mk
  rw [map_add, map_mul, map_intCast, map_intCast, map_add, map_mul, map_intCast, map_intCast,
    oHom_algebraMap, coe_omega]
  have h2 : (((2 : B)) : Closure) = 2 := rfl
  simp [coe_sqrt241, h2]

/-- `√a_i` as an algebraic integer of `genusB`. -/
def rootAO : Fin 4 → 𝓞 genusB :=
  ![''' + ",\n    ".join(prodO(f[2]) for f in FORMS) + ''']

/-- `√b_i` as an algebraic integer of `genusB`. -/
def rootBO : Fin 4 → 𝓞 genusB :=
  ![''' + ",\n    ".join(prodO(f[3]) for f in FORMS) + ''']

theorem oHom_rootAO (i : Fin 4) : oHom (rootAO i) = rootA i := by
  fin_cases i <;> simp [rootAO, rootA, map_mul]

theorem oHom_rootBO (i : Fin 4) : oHom (rootBO i) = rootB i := by
  fin_cases i <;> simp [rootBO, rootB, map_mul]
'''
tail = '''
/-- **`√β_i ∈ Ω`** for the four forms. -/
theorem wideRoot_mem_Omega (i : Fin 4) : wideRoot i ∈ Omega := by
  fin_cases i
  · exact wideRoot_mem_OmegaBcl_0
  · exact wideRoot_mem_OmegaBcl_1
  · exact wideRoot_mem_OmegaBcl_2
  · exact wideRoot_mem_OmegaBcl_3

/-- **`E_W ≤ Ω`.** -/
theorem field_le_Omega : CanonicalWide.field ≤ Omega := by
  rw [CanonicalWide.field, IntermediateField.adjoin_le_iff]
  rintro x (rfl | (⟨k, rfl⟩ | ⟨i, rfl⟩))
  · exact baseRoot_mem_Omega
  · exact genusRoot_mem_Omega k
  · exact wideRoot_mem_Omega i

end UnitDistance.Sqrt241.Wide
'''
open(sys.argv[1], "w").write(hdr + "".join(out) + tail)
