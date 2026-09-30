/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairingNondegeneracy

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-! # The local Hilbert pairing as a linear dual embedding -/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalClassFieldTheory LocalClassFieldTheory.Kummer

variable (L : Type) [Field L] [CharZero L]
variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

local instance localHilbertKummerDualModule :
    Module (ZMod (n : ℕ))
      (Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ))) := by
  letI : AddCommGroup (absolutePowerClassModP L (n : ℕ)) :=
    (absolutePowerClassModP L (n : ℕ)).isAddCommGroup
  letI : Module (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)) :=
    (absolutePowerClassModP L (n : ℕ)).isModule
  letI : Semiring (ZMod (n : ℕ)) :=
    (inferInstance : CommRing (ZMod (n : ℕ))).toCommSemiring.toSemiring
  letI : Module (ZMod (n : ℕ)) (ZMod (n : ℕ)) := Semiring.toModule
  letI : SMulCommClass (ZMod (n : ℕ)) (ZMod (n : ℕ)) (ZMod (n : ℕ)) :=
    ⟨fun r s x => by
      change r * (s * x) = s * (r * x)
      ac_rfl⟩
  exact LinearMap.module

/-- A primitive root identifies the `n`-th roots of unity with additive `ZMod n`. -/
noncomputable def localNthRootsEquivMultiplicativeZMod
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    nthRootsSubgroup L (n : ℕ) ≃* Multiplicative (ZMod (n : ℕ)) := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let ζ : L := hmu.choose
  let hζ : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hmu.choose_spec
  let hζunit := hζ.isUnit_unit' n.ne_zero
  exact
    (nthRootsSubgroupEquivRootsOfUnity L (n : ℕ)).trans
      ((MulEquiv.subgroupCongr hζunit.zpowers_eq.symm).trans
        hζunit.zmodEquivZPowers.symm.toMultiplicativeRight)

/-- The local Hilbert pairing with its roots-of-unity values written in `ZMod n`. -/
noncomputable def localHilbertPairingZMod
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range) →*
      ((Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range) →*
        Multiplicative (ZMod (n : ℕ))) := by
  let hnL : ((n : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let e := localNthRootsEquivMultiplicativeZMod L n hmu
  let H := localHilbertPairing L n hnL hmu
  exact
  { toFun := fun a ↦ e.toMonoidHom.comp (H a)
    map_one' := by
      apply MonoidHom.ext
      intro b
      change e (H 1 b) = 1
      rw [H.map_one]
      exact e.map_one
    map_mul' := by
      intro a c
      apply MonoidHom.ext
      intro b
      change e (H (a * c) b) = e (H a b) * e (H c b)
      rw [H.map_mul]
      exact e.map_mul (H a b) (H c b) }

/-- The Hilbert character of one local power class, regarded as a linear functional. -/
noncomputable def localHilbertLinearFunctional
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty)
    (a : absolutePowerClassModP L (n : ℕ)) :
    Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)) := by
  letI : AddCommGroup
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)) :=
    Additive.addCommGroup
  letI : AddZeroClass
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)) :=
    (inferInstance : AddCommGroup
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range))).toAddGroup.toAddZeroClass
  letI : Module (ZMod (n : ℕ))
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)) :=
    additiveZModModuleOfPowEqOne (n : ℕ)
      (absolutePowerClassQuotient_pow_eq_one L (n : ℕ))
  letI : Semiring (ZMod (n : ℕ)) :=
    (inferInstance : CommRing (ZMod (n : ℕ))).toCommSemiring.toSemiring
  letI : Module (ZMod (n : ℕ)) (ZMod (n : ℕ)) := Semiring.toModule
  exact @AddMonoidHom.toZModLinearMap
    (n : ℕ)
    (Additive (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range))
    (ZMod (n : ℕ)) _ _ _ Semiring.toModule
    ((localHilbertPairingZMod L n hmu (Additive.toMul a)).toAdditiveLeft)

/-- The local Hilbert pairing, curried as a `ZMod n`-linear map into the dual. -/
noncomputable def localHilbertDualEmbedding
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    absolutePowerClassModP L (n : ℕ) →ₗ[ZMod (n : ℕ)]
      Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)) := by
  letI : AddCommGroup
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)) :=
    Additive.addCommGroup
  letI : AddZeroClass
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)) :=
    (inferInstance : AddCommGroup
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range))).toAddGroup.toAddZeroClass
  letI : Module (ZMod (n : ℕ))
      (Additive
        (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)) :=
    additiveZModModuleOfPowEqOne (n : ℕ)
      (absolutePowerClassQuotient_pow_eq_one L (n : ℕ))
  letI : AddCommGroup (absolutePowerClassModP L (n : ℕ)) :=
    (absolutePowerClassModP L (n : ℕ)).isAddCommGroup
  letI : Module (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)) :=
    (absolutePowerClassModP L (n : ℕ)).isModule
  letI : Semiring (ZMod (n : ℕ)) :=
    (inferInstance : CommRing (ZMod (n : ℕ))).toCommSemiring.toSemiring
  letI : Module (ZMod (n : ℕ)) (ZMod (n : ℕ)) := Semiring.toModule
  letI : SMulCommClass (ZMod (n : ℕ)) (ZMod (n : ℕ)) (ZMod (n : ℕ)) :=
    ⟨fun r s x => by
      change r * (s * x) = s * (r * x)
      ac_rfl⟩
  letI : AddCommGroup
      (Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ))) :=
    @LinearMap.addCommGroup
      (ZMod (n : ℕ)) (ZMod (n : ℕ))
      (absolutePowerClassModP L (n : ℕ)) (ZMod (n : ℕ))
      _ _ _ _
      (absolutePowerClassModP L (n : ℕ)).isModule
      Semiring.toModule
      (RingHom.id (ZMod (n : ℕ)))
  letI : AddZeroClass
      (Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ))) :=
    (inferInstance : AddCommGroup
      (Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)))).toAddGroup.toAddZeroClass
  let f :
      Additive
          (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range) →+
        Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)) :=
  { toFun := localHilbertLinearFunctional L n hmu
    map_zero' := by
      apply LinearMap.ext
      intro b
      change (localHilbertPairingZMod L n hmu 1 (Additive.toMul b)).toAdd = 0
      rw [map_one]
      rfl
    map_add' := by
      intro a c
      apply LinearMap.ext
      intro b
      change
        (localHilbertPairingZMod L n hmu
          (Additive.toMul a * Additive.toMul c) (Additive.toMul b)).toAdd =
        (localHilbertPairingZMod L n hmu
          (Additive.toMul a) (Additive.toMul b)).toAdd +
        (localHilbertPairingZMod L n hmu
          (Additive.toMul c) (Additive.toMul b)).toAdd
      rw [map_mul]
      rfl }
  exact @AddMonoidHom.toZModLinearMap
    (n : ℕ)
    (Additive (Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range))
    (Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP L (n : ℕ)))
    _ _ _ (localHilbertKummerDualModule L n) f

@[simp]
theorem localHilbertDualEmbedding_apply
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty)
    (a b : absolutePowerClassModP L (n : ℕ)) :
    localHilbertDualEmbedding L n hmu a b =
      (localHilbertPairingZMod L n hmu
        (Additive.toMul a) (Additive.toMul b)).toAdd :=
  rfl

/-- Nondegeneracy makes the dual-valued local Hilbert map injective. -/
theorem localHilbertDualEmbedding_injective
    (hmu : (primitiveRoots (n : ℕ) L).Nonempty) :
    Function.Injective (localHilbertDualEmbedding L n hmu) := by
  intro a c hac
  apply Additive.toMul.injective
  apply localHilbertPairing_injective_left L n
    (Nat.cast_ne_zero.mpr n.ne_zero) hmu
  apply MonoidHom.ext
  intro b
  apply (localNthRootsEquivMultiplicativeZMod L n hmu).injective
  apply Multiplicative.toAdd.injective
  exact LinearMap.congr_fun hac (Additive.ofMul b)

end ClassFieldTower.Martinet.Shafarevich
