module

public import UnitDistance.Sqrt241.Geometry.QuadraticRootField
public import UnitDistance.ImaginarySevenUnramified

@[expose] public section
set_option backward.privateInPublic true


/-!
# `F(i)/F` is unramified at all finite primes when `√d ∈ F`

Copy of `UnitDistance.ImaginarySevenUnramified` for an admissible radicand `d`
(a prime with `d % 4 = 3`) in place of `7`. The integral primitive element
`τ = (√d + i)/2` is a root of `X² - √d X + (d+1)/4`, and its derivative
`2τ - √d = i` is a unit, so the relative different is the unit ideal.
For `d = 3`, `τ = ζ₁₂` and the polynomial is `X² - √3 X + 1`.
The radicand-free lemma `aeval_derivative_mem_different_of_aeval_zero` is
used from the original.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.ImaginaryRoot
open NumberField Polynomial UnitDistance.KummerInvariant UnitDistance.Sqrt241.QuadraticRoot
variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
variable {d : ℕ} [hd : Fact (Admissible d)]

/-- The constant term `(d+1)/4` of the minimal polynomial of `(√d+i)/2`. -/
def rootConstant (d : ℕ) : ℕ := (d+1)/4

omit hd in
theorem four_mul_rootConstant (h : d % 4 = 3) : 4*rootConstant d = d+1 := by
  unfold rootConstant
  omega

variable (r : F) (hr : r^2=(d : F)) (i : K) (hi : i^2= -1)

def rootInteger : 𝓞 F := ⟨r,by
  apply IsIntegral.of_pow (n:=2) (by decide)
  rw [hr]
  simpa using (isIntegral_algebraMap (R:=ℤ) (A:=F) (x:=(d : ℤ)))⟩

def tau : K := (algebraMap F K r+i)/2

def polynomial : (𝓞 F)[X] :=
  X^2-C (rootInteger F r hr)*X+C ((rootConstant d : ℕ) : 𝓞 F)

omit [NumberField F] hd in
theorem polynomial_monic : (polynomial F r hr).Monic := by
  unfold polynomial
  monicity <;> norm_num

include hd hr hi in
theorem tau_equation :
    (tau F K r i)^2-algebraMap F K r*tau F K r i+((rootConstant d : ℕ) : K)=0 := by
  have hrK : (algebraMap F K r)^2=(d : K) := by rw [←map_pow,hr,map_natCast]
  have hk : (4 : K)*((rootConstant d : ℕ) : K)=(d : K)+1 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : K)) (four_mul_rootConstant hd.out.mod_four)
  dsimp [tau]
  field_simp
  linear_combination hi-hrK+hk

include hd hr hi in
theorem tau_integral : IsIntegral (𝓞 F) (tau F K r i) := by
  refine ⟨polynomial F r hr,polynomial_monic F r hr,?_⟩
  simpa [polynomial,rootInteger,map_natCast,IsScalarTower.algebraMap_apply (𝓞 F) F K] using
    tau_equation F K r hr i hi

def integralTau : 𝓞 K := ⟨tau F K r i,isIntegral_trans (A:=𝓞 F) _ (tau_integral F K r hr i hi)⟩

theorem integralTau_aeval : aeval (integralTau F K r hr i hi) (polynomial F r hr)=0 := by
  apply RingOfIntegers.coe_injective
  simpa [polynomial,rootInteger,integralTau,map_natCast,
    ←IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
    IsScalarTower.algebraMap_apply (𝓞 F) F K] using tau_equation F K r hr i hi

theorem tau_twice_sub : 2*tau F K r i-algebraMap F K r=i := by
  dsimp [tau]
  field_simp
  ring

variable [Fact (Nonsquare (-1:F))] (hquad : Module.finrank F K=2)

include hquad in
theorem integralTau_generates : Algebra.adjoin F {(integralTau F K r hr i hi:K)}=⊤ := by
  let A := Algebra.adjoin F {(integralTau F K r hr i hi:K)}
  have ht : tau F K r i∈A := Algebra.subset_adjoin (Set.mem_singleton _)
  have hI : i∈A := by
    rw [←tau_twice_sub F K r i]
    exact A.sub_mem (A.mul_mem (by simp) ht) (A.algebraMap_mem r)
  let e := ConjugationQuadratic.imaginaryEquiv (F:=F) i hi hquad
  apply top_unique
  intro z _
  obtain ⟨z,rfl⟩ := e.surjective z
  have hz : z=algebraMap F (Extension (-1:F)) z.re+
      algebraMap F (Extension (-1:F)) z.im*QuadraticAlgebra.omega := by
    ext <;> simp
  rw [hz,map_add,map_mul,e.commutes,e.commutes,
    show e QuadraticAlgebra.omega=i from ConjugationQuadratic.imaginaryEquiv_root i hi hquad]
  change algebraMap F K z.re+algebraMap F K z.im*i∈A
  exact A.add_mem (A.algebraMap_mem _) (A.mul_mem (A.algebraMap_mem _) hI)

include r hr i hi hquad in
theorem different_eq_top : differentIdeal (𝓞 F) (𝓞 K)=⊤ := by
  let t := integralTau F K r hr i hi
  let v : 𝓞 K := 2*t-algebraMap (𝓞 F) (𝓞 K) (rootInteger F r hr)
  have hv : (v:K)=i := tau_twice_sub F K r i
  have hmem : v∈differentIdeal (𝓞 F) (𝓞 K) := by
    have hh := UnitDistance.ImaginarySeven.aeval_derivative_mem_different_of_aeval_zero F K t
      (integralTau_generates F K r hr i hi hquad) (polynomial F r hr)
      (integralTau_aeval F K r hr i hi)
    norm_num [polynomial] at hh
    simpa only [map_ofNat] using hh
  apply Ideal.eq_top_of_isUnit_mem _ hmem
  apply isUnit_iff_exists_inv.mpr
  refine ⟨-v,?_⟩
  apply RingOfIntegers.coe_injective
  change (v:K)*(-(v:K))=1
  rw [hv]
  linear_combination -hi

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

include r hr i hi hquad in
/-- Finite unramifiedness is derived from the two displayed roots and the
genuine quadratic degree. -/
theorem finiteUnramified : NumberFieldAnalysis.FiniteUnramified F K := by
  intro P hP
  let := hP
  apply not_dvd_differentIdeal_iff.mp
  rw [different_eq_top F K r hr i hi hquad]
  intro h
  exact hP.ne_top (top_unique (Ideal.dvd_iff_le.mp h))

end UnitDistance.Sqrt241.ImaginaryRoot

namespace UnitDistance.Sqrt241.ImaginaryRoot
open NumberField NumberField.InfinitePlace UnitDistance.Sqrt241.QuadraticRoot
variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
variable {d : ℕ} [hd : Fact (Admissible d)]

/-- The real-place hypothesis supplies nonsquareness, so no separate quadratic
presentation or finite-unramifiedness premise is required. -/
theorem finiteUnramified_of_real_place (r : F) (hr : r^2=(d : F)) (i : K) (hi : i^2= -1)
    (hquad : Module.finrank F K=2) (hreal : 0<nrRealPlaces F) :
    NumberFieldAnalysis.FiniteUnramified F K := by
  classical
  have : Nonempty {w : InfinitePlace F // IsReal w} := Fintype.card_pos_iff.mp hreal
  let w := Classical.choice (inferInstance : Nonempty {w : InfinitePlace F // IsReal w})
  let ψ := embedding_of_isReal w.property
  let : Fact (UnitDistance.KummerInvariant.Nonsquare (-1:F)) := ⟨by
    intro x hx
    have hs := congrArg ψ hx
    simp only [map_pow,map_neg,map_one] at hs
    nlinarith [sq_nonneg (ψ x)]⟩
  exact finiteUnramified F K r hr i hi hquad

end UnitDistance.Sqrt241.ImaginaryRoot
