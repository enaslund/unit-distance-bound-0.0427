module

public import UnitDistance.DyadicLiteralPresentation
public import UnitDistance.DyadicGroup
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Presentations.Profinite
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section
set_option backward.privateInPublic true


/-! The seven literal dyadic relators give the exact closed kernel of every
continuous labeled quotient onto the actual order-thirty-two model. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace UnitDistance.Dyadic.Presentation
open ProCGroups.Presentations
variable {G : Type*} [Group G]

@[simp] theorem comm_eq_one_iff (x y : G) : comm x y=1 ↔ Commute x y := by
  change x⁻¹*y⁻¹*x*y=1 ↔ x*y=y*x
  simp only [mul_assoc,inv_mul_eq_iff_eq_mul,mul_one]

def literalRelations (x y z : G) : Fin 7 → G :=
  ![x^2,y^2,comm x y,comm x z,comm (comm y z) z,z^4,(comm y z)^2]

@[simp] theorem map_comm {H : Type*} [Group H] (f : G →* H) (x y : G) :
    f (comm x y)=comm (f x) (f y) := by simp [comm]

@[simp] theorem map_literalRelations {H : Type*} [Group H] (f : G →* H)
    (x y z : G) (i : Fin 7) :
    f (literalRelations x y z i)=literalRelations (f x) (f y) (f z) i := by
  fin_cases i <;> simp [literalRelations]

theorem model_literalRelations : ∀i,literalRelations D.x D.y D.z i=1 := by decide +kernel

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  (x y z : G)
  (hgen : (Subgroup.closure ({x,y,z}:Set G)).topologicalClosure=⊤)

include hgen in
/-- Exact closed normal generation, proved by collecting the quotient and
comparing with the independently defined thirty-two-element group. -/
theorem closedNormalClosure_literalRelations
    (f : G →* D) (hfclosed : IsClosed (f.ker : Set G)) (hfsurj : Function.Surjective f)
    (hfx : f x=D.x) (hfy : f y=D.y) (hfz : f z=D.z) :
    closedNormalClosure (Set.range (literalRelations x y z))=f.ker := by
  let R := closedNormalClosure (Set.range (literalRelations x y z))
  letI : R.Normal := inferInstanceAs (closedNormalClosure _).Normal
  letI : IsClosed (R : Set G) := closedNormalClosure_isClosed _
  let q : G →* G ⧸ R := QuotientGroup.mk' R
  have hR : R≤f.ker := by
    apply closedNormalClosure_le_closed_normal hfclosed
    rintro r ⟨i,rfl⟩
    change f (literalRelations x y z i)=1
    rw [map_literalRelations,hfx,hfy,hfz]
    exact model_literalRelations i
  have hqrel (i : Fin 7) : literalRelations (q x) (q y) (q z) i=1 := by
    rw [←map_literalRelations]
    exact (QuotientGroup.eq_one_iff _).mpr (subset_closedNormalClosure _ ⟨i,rfl⟩)
  have hqgen : (Subgroup.closure ({q x,q y,q z}:Set (G ⧸ R))).topologicalClosure=⊤ := by
    have h := DenseRange.topologicalClosure_map_subgroup
      (QuotientGroup.continuous_mk (N := R)) (QuotientGroup.mk'_surjective R).denseRange hgen
    simpa only [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton] using h
  have hqx : (q x)^2=1 := hqrel 0
  have hqy : (q y)^2=1 := hqrel 1
  have hqxy : Commute (q x) (q y) := (comm_eq_one_iff _ _).mp (hqrel 2)
  have hqxz : Commute (q x) (q z) := (comm_eq_one_iff _ _).mp (hqrel 3)
  have hqwz : Commute (comm (q y) (q z)) (q z) := (comm_eq_one_iff _ _).mp (hqrel 4)
  have hqz : (q z)^4=1 := hqrel 5
  have hqw : (comm (q y) (q z))^2=1 := hqrel 6
  letI : Finite (G ⧸ R) := finite_of_literal_relators _ _ _ hqx hqy hqz hqxy hqxz hqw hqwz hqgen
  have hcard : Nat.card (G ⧸ R)≤32 := card_le_thirty_two _ _ _ hqx hqy hqz hqxy hqxz hqw hqwz hqgen
  let fbar : G ⧸ R →* D := QuotientGroup.lift R f hR
  have hfbar : Function.Surjective fbar := by
    intro d
    obtain ⟨g,hg⟩ := hfsurj d
    exact ⟨q g,hg⟩
  have hinj : Function.Injective fbar := (hfbar.bijective_of_nat_card_le (by
    simpa only [Nat.card_eq_fintype_card,D.card] using hcard)).1
  apply le_antisymm hR
  intro g hg
  have hqg : q g=1 := hinj (by change f g=fbar 1; rw [map_one]; exact hg)
  exact (QuotientGroup.eq_one_iff _).mp hqg

end UnitDistance.Dyadic.Presentation
