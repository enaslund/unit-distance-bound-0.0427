module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination

@[expose] public section
set_option backward.privateInPublic true


/-! A direct degree-two Shapiro zero-detection proof. A local coboundary is
lifted to an actual coinduced coboundary using a right-coset section. -/
noncomputable section
open CategoryTheory
namespace UnitDistance.ArithmeticProP
open groupCohomology
variable {R G : Type} [CommRing R] [Group G] (H : Subgroup G) (A : Rep R H)

/-- Actual evaluation at the identity after restriction to the subgroup. -/
def coindEvaluationRepHom : Rep.res H.subtype (Rep.coind H.subtype A) ⟶ A := by
  apply Rep.ofHom
  refine ⟨{
    toFun := fun f => f.1 1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl },?_⟩
  intro h
  apply LinearMap.ext
  intro f
  change f.1 (1 * (h : G)) = A.ρ h (f.1 1)
  simpa using f.2 h 1

/-- A degree-two cocycle in a coinduced module is a coboundary whenever
its subgroup restriction evaluated at the identity is a coboundary. -/
theorem coind_cocycle_is_coboundary_of_evaluation
    (f : cocycles₂ (Rep.coind H.subtype A))
    (hf : ∃ b : H → A, ∀ a d : H,
      (f ((a : G),(d : G))).1 1 = A.ρ a (b d) - b (a*d) + b a) :
    (f : G × G → Rep.coind H.subtype A) ∈ coboundaries₂ (Rep.coind H.subtype A) := by
  classical
  obtain ⟨b,hb⟩ := hf
  letI := QuotientGroup.rightRel H
  choose i hi using Quotient.mk'_surjective (α := G)
  let t (x : G) := i (Quotient.mk' x)
  let γ (x : G) : H := ⟨x * (t x)⁻¹,
    QuotientGroup.rightRel_apply.mp (Quotient.eq'.mp (hi (Quotient.mk' x)))⟩
  have hmk (a : H) (x : G) : Quotient.mk' ((a : G)*x) = Quotient.mk' x :=
    Quotient.eq'.mpr (QuotientGroup.rightRel_apply.mpr (by simp))
  have ht (a : H) (x : G) : t ((a : G)*x) = t x := by simp only [t,hmk]
  have hγ (a : H) (x : G) : γ ((a : G)*x) = a * γ x := by
    apply Subtype.ext
    simp [γ,ht,mul_assoc]
  have hγt (x : G) : (γ x : G) * t x = x := by simp [γ]
  have hc (x g h y : G) :
      (f (x*g,h)).1 y + (f (x,g)).1 y =
        (f (g,h)).1 (y*x) + (f (x,g*h)).1 y := by
    exact congrArg (fun z : Rep.coind H.subtype A => z.1 y)
      ((mem_cocycles₂_iff _).mp f.property x g h)
  have he (g h : G) (a : H) (x : G) :
      (f (g,h)).1 ((a : G)*x) = A.ρ a ((f (g,h)).1 x) := (f (g,h)).2 a x
  have he1 (g h : G) (a : H) :
      (f (g,h)).1 (a : G) = A.ρ a ((f (g,h)).1 1) := by
    simpa using he g h a 1
  let C (x : G) : A := (f ((γ x : G),t x)).1 1 - b (γ x)
  have hC (a : H) (x : G) :
      C ((a : G)*x) - A.ρ a (C x) = (f ((a : G),x)).1 1 - b a := by
    dsimp only [C]
    rw [hγ,ht]
    have hc' := hc (a : G) (γ x : G) (t x) 1
    simp only [one_mul,hγt] at hc'
    rw [he1 _ _ a,hb a (γ x)] at hc'
    simp only [map_sub]
    linear_combination (norm := module) hc'
  let B (g : G) : Rep.coind H.subtype A :=
    ⟨fun x => (f (x,g)).1 1 - (C (x*g)-C x),by
      intro a x
      have hc' := hc (a : G) x g 1
      simp only [one_mul] at hc'
      rw [he1 _ _ a] at hc'
      have h1 := hC a (x*g)
      have h2 := hC a x
      simp only [map_sub]
      change (f ((a : G)*x,g)).1 1 - (C (((a : G)*x)*g)-C ((a : G)*x)) =
        A.ρ a ((f (x,g)).1 1) - (A.ρ a (C (x*g))-A.ρ a (C x))
      rw [mul_assoc]
      linear_combination (norm := module) hc' - h1 + h2⟩
  refine ⟨B,?_⟩
  funext gh
  apply Subtype.ext
  funext x
  change ((B gh.2).1 (x*gh.1) - (B (gh.1*gh.2)).1 x + (B gh.1).1 x) = (f gh).1 x
  dsimp only [B]
  have hc' := hc x gh.1 gh.2 1
  simp only [one_mul] at hc'
  rw [mul_assoc]
  linear_combination (norm := module) hc'

/-- The actual restriction/evaluation map on H² is injective. -/
theorem coindEvaluationH2_injective :
    Function.Injective
      (groupCohomology.map H.subtype (coindEvaluationRepHom H A) 2).hom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨f,rfl⟩ := ((ModuleCat.epi_iff_surjective (H2π (Rep.coind H.subtype A))).mp inferInstance) x
  rw [H2π_comp_map_apply,H2π_eq_zero_iff] at hx
  apply (H2π_eq_zero_iff _).mpr
  apply coind_cocycle_is_coboundary_of_evaluation H A f
  obtain ⟨b,hb⟩ := hx
  refine ⟨b,?_⟩
  intro a d
  have h := congrFun hb (a,d)
  exact h.symm

end UnitDistance.ArithmeticProP
