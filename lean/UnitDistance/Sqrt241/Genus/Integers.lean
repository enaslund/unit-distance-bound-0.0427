module

public import UnitDistance.Sqrt241.Genus.Galois
public import UnitDistance.Sqrt241.Genus.Frobenius

@[expose] public section
set_option backward.privateInPublic true


/-!
# Explicit integers of the canonical genus field

`bHom : ℚ(√241) → E` (as `QuadraticAlgebra ℚ 241 0`), and the elements
`√241`, the radicands, their conjugates and the genus roots as elements of
`𝓞 E`.  Identities in `𝓞 E` are checked in the closure (`ext_closure`), and
identities in `B` coordinatewise in `QuadraticAlgebra ℚ 241 0` (usually by
`decide +kernel`).
-/

noncomputable section
open NumberField IntermediateField

namespace UnitDistance.Sqrt241.Genus

open CanonicalGenus

theorem B_le_field : B ≤ field := tower_le_field 0

/-- `B` inside `E`, as an algebra map from `ℚ(√241)`. -/
def bHom : Q241 →ₐ[ℚ] Carrier where
  toFun z := ⟨ev z, B_le_field (ev_mem z)⟩
  map_one' := Subtype.ext (map_one ev)
  map_mul' z w := Subtype.ext (map_mul ev z w)
  map_zero' := Subtype.ext (map_zero ev)
  map_add' z w := Subtype.ext (map_add ev z w)
  commutes' q := Subtype.ext (ev.commutes q)

@[simp] theorem coe_bHom (z : Q241) : ((bHom z : Carrier) : Closure) = ev z := rfl

theorem bHom_eq (z : Q241) : bHom z = (z.re : Carrier) + (z.im : Carrier) * bE := by
  apply Subtype.ext
  simp [ev_apply]

theorem bHom_radQ (i : Fin 8) : bHom (radQ i) = radE i := by
  apply Subtype.ext
  simp [radE, ← radicand_eq_ev, radicand]

theorem bHom_omega : bHom ⟨0, 1⟩ = bE := by
  apply Subtype.ext
  simp [ev_apply]

theorem aut_bHom_of_fix (σ : Carrier ≃ₐ[ℚ] Carrier) (hσ : σ bE = bE) (z : Q241) :
    σ (bHom z) = bHom z := by
  rw [bHom_eq]
  simp [map_add, map_mul, map_ratCast, hσ]

theorem aut_bHom_of_neg (σ : Carrier ≃ₐ[ℚ] Carrier) (hσ : σ bE = -bE) (z : Q241) :
    σ (bHom z) = bHom (star z) := by
  rw [bHom_eq, bHom_eq]
  simp [map_add, map_mul, map_ratCast, hσ]

/-! ### Integrality -/

theorem isIntegral_of_quadratic {x : Carrier} (t n : ℤ)
    (h : x ^ 2 - (t : Carrier) * x + (n : Carrier) = 0) : IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
    simpa using h

theorem isIntegral_bHom (z : Q241) (h1 : (QuadraticAlgebra.trace z).den = 1)
    (h2 : (QuadraticAlgebra.norm z).den = 1) : IsIntegral ℤ (bHom z) := by
  apply isIntegral_of_quadratic (QuadraticAlgebra.trace z).num (QuadraticAlgebra.norm z).num
  have ht : ((QuadraticAlgebra.trace z).num : ℚ) = QuadraticAlgebra.trace z :=
    Rat.coe_int_num_of_den_eq_one h1
  have hn : ((QuadraticAlgebra.norm z).num : ℚ) = QuadraticAlgebra.norm z :=
    Rat.coe_int_num_of_den_eq_one h2
  have hsqQ := QuadraticAlgebra.sq_eq_trace_smul_sub_norm z
  rw [Algebra.smul_def] at hsqQ
  have hsq := congrArg bHom hsqQ
  rw [map_pow, map_sub, map_mul, AlgHom.commutes, AlgHom.commutes] at hsq
  rw [hsq]
  have e1 : ((QuadraticAlgebra.trace z).num : Carrier) =
      algebraMap ℚ Carrier (QuadraticAlgebra.trace z) := by
    rw [← map_intCast (algebraMap ℚ Carrier), ht]
  have e2 : ((QuadraticAlgebra.norm z).num : Carrier) =
      algebraMap ℚ Carrier (QuadraticAlgebra.norm z) := by
    rw [← map_intCast (algebraMap ℚ Carrier), hn]
  rw [e1, e2]
  ring

/-- Construct an element of `𝓞 E` from an integral element. -/
def toO (x : Carrier) (hx : IsIntegral ℤ x) : 𝓞 Carrier := ⟨x, hx⟩

@[simp] theorem coe_toO (x : Carrier) (hx : IsIntegral ℤ x) : ((toO x hx : 𝓞 Carrier) : Carrier) = x :=
  rfl

/-- The composite `𝓞 E → E → Ω`. -/
def toClosure : 𝓞 Carrier →+* Closure :=
  (field.val.toRingHom).comp (algebraMap (𝓞 Carrier) Carrier)

theorem toClosure_apply (x : 𝓞 Carrier) : toClosure x = (((x : Carrier) : Closure)) := rfl

theorem ext_closure {x y : 𝓞 Carrier}
    (h : (((x : Carrier) : Closure)) = (((y : Carrier) : Closure))) : x = y :=
  RingOfIntegers.ext (Subtype.ext h)

theorem isIntegral_bE : IsIntegral ℤ bE := by
  apply isIntegral_of_quadratic 0 (-241)
  rw [bE_sq]
  push_cast
  ring

def bO : 𝓞 Carrier := toO bE isIntegral_bE

theorem trace_radQ_den (i : Fin 8) : (QuadraticAlgebra.trace (radQ i)).den = 1 := by
  revert i; decide +kernel

theorem norm_radQ_den (i : Fin 8) : (QuadraticAlgebra.norm (radQ i)).den = 1 := by
  revert i; decide +kernel

theorem trace_star_radQ_den (i : Fin 8) : (QuadraticAlgebra.trace (star (radQ i))).den = 1 := by
  revert i; decide +kernel

theorem norm_star_radQ_den (i : Fin 8) : (QuadraticAlgebra.norm (star (radQ i))).den = 1 := by
  revert i; decide +kernel

def radO (i : Fin 8) : 𝓞 Carrier :=
  toO (bHom (radQ i)) (isIntegral_bHom _ (trace_radQ_den i) (norm_radQ_den i))

def conjO (i : Fin 8) : 𝓞 Carrier :=
  toO (bHom (star (radQ i))) (isIntegral_bHom _ (trace_star_radQ_den i) (norm_star_radQ_den i))

theorem isIntegral_gE (i : Fin 8) : IsIntegral ℤ (gE i) := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [gE_sq, ← bHom_radQ]
  exact isIntegral_bHom _ (trace_radQ_den i) (norm_radQ_den i)

def gO (i : Fin 8) : 𝓞 Carrier := toO (gE i) (isIntegral_gE i)

@[simp] theorem coe_bO : (((bO : 𝓞 Carrier) : Carrier) : Closure) = baseRoot := rfl
@[simp] theorem coe_radO (i : Fin 8) :
    (((radO i : 𝓞 Carrier) : Carrier) : Closure) = ev (radQ i) := rfl
@[simp] theorem coe_conjO (i : Fin 8) :
    (((conjO i : 𝓞 Carrier) : Carrier) : Closure) = ev (star (radQ i)) := rfl
@[simp] theorem coe_gO (i : Fin 8) :
    (((gO i : 𝓞 Carrier) : Carrier) : Closure) = genusRoot i := rfl

@[simp] theorem coe_intCast_O (n : ℤ) : ((((n : 𝓞 Carrier) : Carrier) : Closure)) = (n : Closure) := by
  rw [← toClosure_apply, map_intCast]

@[simp] theorem coe_natCast_O (n : ℕ) : ((((n : 𝓞 Carrier) : Carrier) : Closure)) = (n : Closure) := by
  rw [← toClosure_apply, map_natCast]

@[simp] theorem coe_ofNat_O (n : ℕ) [n.AtLeastTwo] :
    ((((OfNat.ofNat n : 𝓞 Carrier) : Carrier) : Closure)) = (OfNat.ofNat n : Closure) := by
  rw [← toClosure_apply, map_ofNat]

@[simp] theorem coe_mul_O (x y : 𝓞 Carrier) :
    ((((x * y : 𝓞 Carrier) : Carrier) : Closure)) =
      (((x : Carrier) : Closure)) * (((y : Carrier) : Closure)) := by
  rw [← toClosure_apply, map_mul]; rfl

@[simp] theorem coe_add_O (x y : 𝓞 Carrier) :
    ((((x + y : 𝓞 Carrier) : Carrier) : Closure)) =
      (((x : Carrier) : Closure)) + (((y : Carrier) : Closure)) := by
  rw [← toClosure_apply, map_add]; rfl

@[simp] theorem coe_sub_O (x y : 𝓞 Carrier) :
    ((((x - y : 𝓞 Carrier) : Carrier) : Closure)) =
      (((x : Carrier) : Closure)) - (((y : Carrier) : Closure)) := by
  rw [← toClosure_apply, map_sub]; rfl

@[simp] theorem coe_neg_O (x : 𝓞 Carrier) :
    ((((-x : 𝓞 Carrier) : Carrier) : Closure)) = -(((x : Carrier) : Closure)) := by
  rw [← toClosure_apply, map_neg]; rfl

@[simp] theorem coe_two_O : ((((2 : 𝓞 Carrier) : Carrier) : Closure)) = 2 := by
  rw [← toClosure_apply, map_ofNat]

@[simp] theorem coe_one_O : ((((1 : 𝓞 Carrier) : Carrier) : Closure)) = 1 := by
  rw [← toClosure_apply, map_one]

@[simp] theorem coe_pow_O (x : 𝓞 Carrier) (n : ℕ) :
    ((((x ^ n : 𝓞 Carrier) : Carrier) : Closure)) = (((x : Carrier) : Closure)) ^ n := by
  rw [← toClosure_apply, map_pow]; rfl

@[simp] theorem coe_smul_O (σ : Carrier ≃ₐ[ℚ] Carrier) (x : 𝓞 Carrier) :
    ((σ • x : 𝓞 Carrier) : Carrier) = σ (x : Carrier) := rfl

theorem radO_mul_conjO (i : Fin 8) : radO i * conjO i = ((normValue i : ℤ) : 𝓞 Carrier) := by
  apply ext_closure
  rw [coe_mul_O, coe_radO, coe_conjO, ← radicand_eq_ev, ← conjRadicand, radicand_mul_conj,
    coe_intCast_O]

theorem gO_sq (i : Fin 8) : gO i * gO i = radO i := by
  apply ext_closure
  rw [coe_mul_O, coe_gO, coe_radO, ← radicand_eq_ev, ← genusRoot_sq, sq]

theorem bO_sq : bO * bO = (241 : 𝓞 Carrier) := by
  apply ext_closure
  rw [coe_mul_O, coe_bO, ← sq, baseRoot_sq, coe_ofNat_O]

end UnitDistance.Sqrt241.Genus
