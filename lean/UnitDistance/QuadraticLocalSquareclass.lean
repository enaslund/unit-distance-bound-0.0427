module

public import UnitDistance.QuadraticRamification

@[expose] public section
set_option backward.privateInPublic true


/-! Actual quadratic ramification using an integral local-unit representative
of the radicand's squareclass. -/
noncomputable section
open NumberField
namespace UnitDistance.QuadraticRamification
open KummerInvariant
variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in
/-- Multiplication by a nonzero square preserves nonsquareness. -/
theorem nonsquare_mul_sq {q c : F} (hq : Nonsquare q) (hc : c ≠ 0) :
    Nonsquare (q*c^2) := by
  intro z hz
  apply hq (z/c)
  rw [div_pow,hz]
  exact mul_div_cancel_right₀ q (pow_ne_zero 2 hc)

/-- An integral local unit in the radicand's squareclass excludes ramification.
The actual carrier remains `Extension q`, including all its field instances. -/
theorem extension_isUnramifiedAt_of_local_squareclass
    (q : F) [Fact (Nonsquare q)] (a : 𝓞 F) (c : F) (hc : c ≠ 0)
    (ha : (a:F) = q*c^2)
    (P : Ideal (𝓞 (Extension q))) [P.IsPrime]
    (h2 : (2:𝓞 (Extension q)) ∉ P)
    (haP : algebraMap (𝓞 F) (𝓞 (Extension q)) a ∉ P) :
    Algebra.IsUnramifiedAt (𝓞 F) P := by
  let L := Extension q
  let y : L := algebraMap F L c * QuadraticAlgebra.omega
  have hsq : y^2 = algebraMap F L (a:F) := by
    have homega : (QuadraticAlgebra.omega:L)^2 = algebraMap F L q := by
      ext <;> simp [pow_two,L]
    dsimp [y]
    rw [mul_pow,homega,←map_pow,←map_mul,ha]
    ring_nf
  let x : 𝓞 L := ⟨y,by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hsq]
    exact map_isIntegral_int (algebraMap F L) a.property⟩
  have hx : x^2 = algebraMap (𝓞 F) (𝓞 L) a := by
    apply RingOfIntegers.coe_injective
    exact hsq
  have hgen : Algebra.adjoin F {(x:L)} = ⊤ := by
    apply top_unique
    intro z _
    have he : z = algebraMap F L z.re + algebraMap F L (z.im/c)*(x:L) := by
      ext <;> simp [x,y,L,QuadraticAlgebra.omega,hc]
      field_simp [hc]
    rw [he]
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Algebra.subset_adjoin (Set.mem_singleton _)))
  exact isUnramifiedAt_of_not_mem F L a
    (ha ▸ nonsquare_mul_sq F (Fact.out : Nonsquare q) hc) x hx hgen P h2 haP

end UnitDistance.QuadraticRamification
