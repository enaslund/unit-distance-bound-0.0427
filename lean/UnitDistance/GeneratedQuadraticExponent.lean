module

public import UnitDistance.GeneratedQuadraticGalois

@[expose] public section
set_option backward.privateInPublic true


/-! Actual squares in invariant quadratic towers over an elementary
involutive Galois base, and the resulting exponent-four conclusion. -/
noncomputable section
namespace UnitDistance.Multiquadratic
universe u
variable {ι : Type*} [DecidableEq ι] {E : Type u} [Field E] [CharZero E]
  {k : Type*} [Field k] [Algebra k E] [IsGalois k E]
  {a : ι → E} {s : Finset ι} (T : GeneratedGaloisTower k a s)
  (hbase : ∀ σ : Gal(E/k), Function.Involutive σ)

include hbase in
theorem GeneratedGaloisTower.aut_square_fixes_base (σ : Gal(T.Carrier/k)) (x : E) :
    (σ^2) (algebraMap E T.Carrier x)=algebraMap E T.Carrier x := by
  change σ (σ (algebraMap E T.Carrier x))=algebraMap E T.Carrier x
  rw [← AlgEquiv.restrictNormal_commutes σ E x,
    ← AlgEquiv.restrictNormal_commutes σ E (σ.restrictNormal E x),hbase]

include hbase in
theorem GeneratedGaloisTower.aut_pow_four (σ : Gal(T.Carrier/k)) : σ^4=1 := by
  have h := T.aut_sq_eq_one (σ^2) (T.aut_square_fixes_base hbase σ)
  simpa only [← pow_mul] using h

include hbase in
theorem GeneratedGaloisTower.aut_square_commute
    (hinvariant : ∀ i ∈ s, ∀ τ : Gal(E/k), ∃ u : E, a i*u^2=τ (a i))
    (σ τ : Gal(T.Carrier/k)) : Commute (σ^2) τ :=
  T.aut_commute hinvariant (σ^2) τ (T.aut_square_fixes_base hbase σ)

end UnitDistance.Multiquadratic
