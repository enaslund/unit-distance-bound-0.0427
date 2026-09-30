module

public import UnitDistance.PadicTwoQuadraticRelation

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The image of the genuine ℚ₂ relation in any bilinear class-two group

`FreeThreeQuadratic.Q` (order `2⁹`) is the universal three-generator
characteristic-2 class-two group: for any `ZMod 2`-bilinear law `β` and any
three elements `g i` of `GroupModel β` there is a homomorphism
`threeHom β g : FreeThreeQuadratic.Q →* GroupModel β` with
`basis i ↦ g i` (explicit formula; the homomorphism property is the
polarization identity of the quadratic correction `quad`).

Consequently a continuous map `ψ` from the free pro-2 group on `a, b, c` to a
pro-2 `GroupModel β` factors through `PadicTwoQuadraticRelation.detector`,
and the genuine relation `r` (detector value `a² [b, c]`) maps to the central
element `β(ā, ā) + β(b̄, c̄) - β(c̄, b̄)` (`genuineRelation_image`), where
`ā, b̄, c̄` are the elementary images of the generators.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Presentation

open ClassTwo ProCGroups ProCGroups.ProC

/-- Coordinates of the universal three-generator cocycle: squares `a², b², c²`
at `0, 1, 2`, pairs `(1,0), (2,0), (2,1)` at `3, 4, 5`. -/
theorem freeThree_cocycle_apply : ∀ (u v : FreeThreeQuadratic.V) (k : Fin 6),
    FreeThreeQuadratic.cocycle u v k =
      ![u 0 * v 0, u 1 * v 1, u 2 * v 2, u 1 * v 0, u 2 * v 0, u 2 * v 1] k := by
  decide +kernel

variable {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W) (g : Fin 3 → GroupModel β)

/-- Elementary part of `threeHom`. -/
def threeLin (v : Fin 3 → ZMod 2) : V := ∑ i, v i • (g i).base

/-- Images of the six central basis vectors (squares, then commutators). -/
def threeCentralVec : Fin 6 → W :=
  ![β (g 0).base (g 0).base, β (g 1).base (g 1).base, β (g 2).base (g 2).base,
    β (g 1).base (g 0).base - β (g 0).base (g 1).base,
    β (g 2).base (g 0).base - β (g 0).base (g 2).base,
    β (g 2).base (g 1).base - β (g 1).base (g 2).base]

/-- Central part. -/
def threeCen (w : Fin 6 → ZMod 2) : W := ∑ k, w k • threeCentralVec β g k

/-- Quadratic correction. -/
def threeQuad (v : Fin 3 → ZMod 2) : W :=
  ∑ i, v i • (g i).central + (v 0 * v 1) • β (g 0).base (g 1).base +
    (v 0 * v 2) • β (g 0).base (g 2).base + (v 1 * v 2) • β (g 1).base (g 2).base

/-- The map `FreeThreeQuadratic.Q → GroupModel β`, `basis i ↦ g i`. -/
def threeMap (q : FreeThreeQuadratic.Q) : GroupModel β :=
  ⟨threeLin β g q.base, threeCen β g q.central + threeQuad β g q.base⟩

theorem threeCen_add (w w' : Fin 6 → ZMod 2) :
    threeCen β g (w + w') = threeCen β g w + threeCen β g w' := by
  simp only [threeCen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem threeCen_cocycle (u v : Fin 3 → ZMod 2) :
    threeCen β g (FreeThreeQuadratic.cocycle u v) =
      (u 0 * v 0) • β (g 0).base (g 0).base + (u 1 * v 1) • β (g 1).base (g 1).base +
      (u 2 * v 2) • β (g 2).base (g 2).base +
      (u 1 * v 0) • (β (g 1).base (g 0).base - β (g 0).base (g 1).base) +
      (u 2 * v 0) • (β (g 2).base (g 0).base - β (g 0).base (g 2).base) +
      (u 2 * v 1) • (β (g 2).base (g 1).base - β (g 1).base (g 2).base) := by
  simp only [threeCen, Fin.sum_univ_six, freeThree_cocycle_apply, threeCentralVec]
  simp

theorem threeLin_add (u v : Fin 3 → ZMod 2) :
    threeLin β g (u + v) = threeLin β g u + threeLin β g v := by
  simp only [threeLin, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem threeMap_mul (q q' : FreeThreeQuadratic.Q) :
    threeMap β g (q * q') = threeMap β g q * threeMap β g q' := by
  apply GroupModel.ext
  · simp only [threeMap, GroupModel.mul_base, threeLin_add]
  · simp only [threeMap, GroupModel.mul_central, GroupModel.mul_base, threeCen_add,
      threeCen_cocycle]
    simp only [threeQuad, threeLin, Fin.sum_univ_three, Pi.add_apply, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply]
    module

theorem threeMap_one : threeMap β g 1 = 1 := by
  apply GroupModel.ext
  · simp [threeMap, threeLin]
  · simp [threeMap, threeCen, threeQuad]

/-- The homomorphism `FreeThreeQuadratic.Q →* GroupModel β` with `basis i ↦ g i`. -/
def threeHom : FreeThreeQuadratic.Q →* GroupModel β where
  toFun := threeMap β g
  map_one' := threeMap_one β g
  map_mul' := threeMap_mul β g

theorem threeHom_basis (i : Fin 3) : threeHom β g (FreeThreeQuadratic.basis i) = g i := by
  apply GroupModel.ext
  · change threeLin β g (Pi.single i 1) = (g i).base
    fin_cases i <;> simp [threeLin]
  · change threeCen β g 0 + threeQuad β g (Pi.single i 1) = (g i).central
    fin_cases i <;> simp [threeCen, threeQuad]

theorem threeHom_relation :
    threeHom β g FreeThreeQuadratic.relation =
      ⟨0, β (g 0).base (g 0).base + (β (g 2).base (g 1).base - β (g 1).base (g 2).base)⟩ := by
  apply GroupModel.ext
  · change threeLin β g 0 = 0
    simp [threeLin]
  · change threeCen β g (Pi.single 0 1 + Pi.single 5 1) + threeQuad β g 0 = _
    simp [threeCen, threeQuad, Fin.sum_univ_six, threeCentralVec]

/-- **Image of the genuine relation.** For a continuous map `ψ` from the free
pro-2 group on three generators to a pro-2 bilinear class-two group, every
element `r` with detector value `a²[b,c]` (e.g. the genuine ℚ₂ relation of
`PadicTwoQuadraticRelation.exists_actual_quadratic_relation`) maps to the
central element `β(ā,ā) + β(b̄,c̄) - β(c̄,b̄)`. -/
theorem genuineRelation_image
    [TopologicalSpace (GroupModel β)] [DiscreteTopology (GroupModel β)]
    [IsTopologicalGroup (GroupModel β)] [CompactSpace (GroupModel β)]
    (hQ : HasPGroupOpenNormalBasis 2 (GroupModel β))
    (ψ : PadicTwoQuadraticRelation.Source →ₜ* GroupModel β)
    (r : PadicTwoQuadraticRelation.Source)
    (hr : PadicTwoQuadraticRelation.detector r = FreeThreeQuadratic.relation) :
    ψ r = ⟨0, β (ψ (FiniteFreeProTwo.generator 3 0)).base (ψ (FiniteFreeProTwo.generator 3 0)).base +
      (β (ψ (FiniteFreeProTwo.generator 3 1)).base (ψ (FiniteFreeProTwo.generator 3 2)).base -
        β (ψ (FiniteFreeProTwo.generator 3 2)).base (ψ (FiniteFreeProTwo.generator 3 1)).base)⟩ := by
  let g : Fin 3 → GroupModel β := fun i ↦ ψ (FiniteFreeProTwo.generator 3 i)
  let φ : PadicTwoQuadraticRelation.Source →ₜ* GroupModel β :=
    { toMonoidHom := (threeHom β g).comp PadicTwoQuadraticRelation.detector.toMonoidHom
      continuous_toFun := (continuous_of_discreteTopology :
        Continuous (threeHom β g : PadicTwoQuadraticRelation.U.Q → GroupModel β)).comp
          PadicTwoQuadraticRelation.detector.continuous_toFun }
  have hext := (FiniteFreeProTwo.isFree 3).hom_ext hQ (f := ψ.toMonoidHom) (g := φ.toMonoidHom)
    ψ.continuous_toFun φ.continuous_toFun (by
      intro i
      change g i = threeHom β g (PadicTwoQuadraticRelation.detector (FiniteFreeProTwo.generator 3 i))
      rw [PadicTwoQuadraticRelation.detector_generator, threeHom_basis])
  have h1 : ψ r = threeHom β g FreeThreeQuadratic.relation := by
    have := congrArg (fun f : PadicTwoQuadraticRelation.Source →* GroupModel β ↦ f r) hext
    change ψ r = threeHom β g (PadicTwoQuadraticRelation.detector r) at this
    rw [this, hr]
  rw [h1, threeHom_relation]
  apply GroupModel.ext
  · rfl
  · change β (g 0).base (g 0).base + (β (g 2).base (g 1).base - β (g 1).base (g 2).base) =
      β (g 0).base (g 0).base + (β (g 1).base (g 2).base - β (g 2).base (g 1).base)
    have h2 : ∀ x : W, x + x = 0 := fun x ↦ GroupModel.add_self_of_charTwo (R := ZMod 2) x
    have hneg : ∀ x : W, -x = x := fun x ↦ neg_eq_iff_add_eq_zero.mpr (h2 x)
    rw [sub_eq_add_neg, sub_eq_add_neg, hneg, hneg, add_comm (β (g 2).base (g 1).base)]

end UnitDistance.Sqrt241.Presentation
