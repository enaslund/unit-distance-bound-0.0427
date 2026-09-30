module

public import UnitDistance.QuadraticUnramifiedOutside

@[expose] public section
set_option backward.privateInPublic true


/-! Integral presentation of an actual quadratic radicand. This keeps the
field carrier fixed while proving equality with an integral element. -/
noncomputable section
open NumberField
namespace UnitDistance.QuadraticRamification
open UnitDistance.KummerInvariant
variable (F : Type*) [Field F] [NumberField F]

/-- A chosen radicand equal to an integral element with supported complement
preserves actual ramification support. The carrier is literally `Extension q`. -/
theorem integral_eq_extension_unramifiedAway {N : ℤ}
    (hF : UnramifiedAway F N) (h2 : 2 ∣ N)
    (q : F) (a b : 𝓞 F) (hqa : q = (a:F)) (n : ℤ)
    (hab : a*b = n) (hn : ∃ m : ℕ, n ∣ N^m) [Fact (Nonsquare q)] :
    UnramifiedAway (Extension q) N := by
  let L := Extension q
  have hs : (QuadraticAlgebra.omega : L)^2 = algebraMap F L (a:F) := by
    have he : (QuadraticAlgebra.omega : L)^2 = algebraMap F L q := by
      ext <;> simp [L, pow_two]
    exact he.trans (congrArg (algebraMap F L) hqa)
  let x : 𝓞 L := ⟨QuadraticAlgebra.omega, by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hs]
    exact map_isIntegral_int (algebraMap F L) a.property⟩
  have ha : Nonsquare (a:F) := hqa ▸ (Fact.out : Nonsquare q)
  apply unramifiedAway_of_integral_product F L hF h2 a b n hab hn ha x
  · apply RingOfIntegers.coe_injective
    change (QuadraticAlgebra.omega : L)^2 = algebraMap F L (a:F)
    exact hs
  · apply top_unique
    intro z _
    have he : z = algebraMap F L z.re + algebraMap F L z.im*(x:L) := by
      ext <;> simp [x, L, QuadraticAlgebra.omega]
    rw [he]
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Algebra.subset_adjoin (Set.mem_singleton _)))

/-- Integer constants in an existing field presentation. -/
theorem int_eq_extension_unramifiedAway {N : ℤ} (hF : UnramifiedAway F N) (h2 : 2 ∣ N)
    (q : F) (d : ℤ) (hqd : q = (d:F))
    (hd : ∃ m : ℕ, d ∣ N^m) [Fact (Nonsquare q)] : UnramifiedAway (Extension q) N := by
  apply integral_eq_extension_unramifiedAway F hF h2 q (d:𝓞 F) 1 _ d (by simp) hd
  exact hqd.trans (map_intCast (algebraMap (𝓞 F) F) d).symm

end UnitDistance.QuadraticRamification
