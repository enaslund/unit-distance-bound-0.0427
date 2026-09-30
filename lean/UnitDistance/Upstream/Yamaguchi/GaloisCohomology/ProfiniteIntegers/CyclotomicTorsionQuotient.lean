/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger
public import Mathlib.GroupTheory.Torsion

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The torsion quotient in the cyclotomic decomposition

The cyclotomic torsion calculation uses the decomposition
`Gal(ℚ_cyc/ℚ) ≃ ℤ̂ × f`, where the torsion subgroup is dense in the
second factor.  This file proves the topological-group calculation which
turns that decomposition into a `ℤ̂`-extension.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

/-- The additive group of `ℤ̂` is torsion-free. -/
instance : IsAddTorsionFree ZHat :=
  ⟨fun {_} hn => zHatMulNat_injective (Nat.pos_of_ne_zero hn)⟩

/-- The multiplicative presentation of additive `ℤ̂` is torsion-free. -/
instance : IsMulTorsionFree (Multiplicative ZHat) :=
  inferInstance

/-- In a product `ℤ̂ × T` whose torsion is dense in `T`, the closure of
the torsion subgroup is precisely the second factor. -/
theorem topologicalClosure_torsion_zHatMul_prod
    (T : Type*) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T]
    (hT : Dense (CommGroup.torsion T : Set T)) :
    (CommGroup.torsion (Multiplicative ZHat × T)).topologicalClosure =
      (⊥ : Subgroup (Multiplicative ZHat)).prod (⊤ : Subgroup T) := by
  rw [CommGroup.torsion_prod,
    (CommGroup.isMulTorsionFree_iff_torsion_eq_bot.mp inferInstance)]
  apply SetLike.ext'
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_prod,
    closure_prod_eq]
  simp only [Subgroup.coe_bot, hT.closure_eq]
  rw [closure_singleton]
  ext x
  simp [Subgroup.mem_prod]

/-- Algebraic quotient form of the cyclotomic torsion decomposition: after a cyclotomic decomposition
with dense torsion factor, quotienting by the closure of torsion leaves
the `ℤ̂` factor. -/
noncomputable def torsionQuotientZHatMulProdEquiv
    (T : Type*) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T]
    (hT : Dense (CommGroup.torsion T : Set T)) :
    (Multiplicative ZHat × T) ⧸
        (CommGroup.torsion (Multiplicative ZHat × T)).topologicalClosure ≃*
      Multiplicative ZHat := by
  rw [topologicalClosure_torsion_zHatMul_prod T hT]
  let fstHom : Multiplicative ZHat × T →* Multiplicative ZHat :=
    MonoidHom.fst _ _
  have hker :
      fstHom.ker =
        (⊥ : Subgroup (Multiplicative ZHat)).prod (⊤ : Subgroup T) := by
    ext x
    simp [fstHom, Subgroup.mem_prod]
  rw [← hker]
  exact QuotientGroup.quotientKerEquivOfSurjective
    fstHom Prod.fst_surjective

end ClassFormation
