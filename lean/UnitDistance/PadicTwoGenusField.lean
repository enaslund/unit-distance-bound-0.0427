module

public import UnitDistance.PadicTwoSquareclassIndependence
public import UnitDistance.GeneratedQuadraticSigns

@[expose] public section
set_option backward.privateInPublic true


/-! A degree-eight actual Q₂ genus field, with all independent sign automorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.PadicTwoGenus
open Multiquadratic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def radicands (i : Fin 3) : ℚ_[2] := PadicTwo.independentRadicand i

theorem radicands_ne_zero (i : Fin 3) : radicands i≠0 := by
  fin_cases i <;> norm_num [radicands,PadicTwo.independentRadicand]

theorem products_nonsquare (s : Finset (Fin 3)) (hs : s.Nonempty) :
    ¬IsSquare (∏ i ∈ s,radicands i) := by
  let w : Fin 3 → ZMod 2 := fun i => if i∈s then 1 else 0
  have he : (∏ i,radicands i^(w i).val)=∏ i∈s,radicands i := by
    classical
    have ht (i : Fin 3) : radicands i^(w i).val = if i∈s then radicands i else 1 := by
      by_cases hi : i∈s <;> simp [w,hi,show (1 : ZMod 2).val=1 from rfl]
    simp_rw [ht]
    simp
  intro h
  have hh : IsSquare (∏ i,radicands i^(w i).val) := he.symm ▸ h
  have hz := PadicTwo.independent_products w hh
  obtain ⟨i,hi⟩ := hs
  have hh := congrFun hz i
  simp [w,hi,show (1 : ZMod 2).val=1 from rfl] at hh

def genusTower : GeneratedGaloisTower ℚ_[2] radicands Finset.univ :=
  Classical.choice (exists_generatedGaloisTower ℚ_[2] radicands radicands_ne_zero
    products_nonsquare (fun i σ => ⟨1,by simpa using (σ.commutes (radicands i)).symm⟩) Finset.univ)

abbrev GenusField := genusTower.Carrier
instance : Field GenusField := genusTower.field
instance : CharZero GenusField := genusTower.charZero
instance : Algebra ℚ_[2] GenusField := genusTower.algebra
instance : Module.Finite ℚ_[2] GenusField := genusTower.finite
instance : IsGalois ℚ_[2] GenusField := genusTower.galois

theorem degree : Module.finrank ℚ_[2] GenusField=8 := by simpa using genusTower.degree

theorem has_root (i : Fin 3) : ∃x : GenusField,x^2=algebraMap ℚ_[2] GenusField (radicands i) := by
  obtain ⟨x,hx⟩ := genusTower.toActualGaloisTower.toActualTower.isSquare_radical i
    (Finset.mem_univ i) (radicands_ne_zero i)
  exact ⟨x,by simpa [pow_two] using hx.symm⟩

def roots (i : Fin 3) : GenusField := (has_root i).choose

theorem roots_sq (i : Fin 3) : (roots i)^2=algebraMap ℚ_[2] GenusField (radicands i) :=
  (has_root i).choose_spec

theorem roots_sq_int (i : Fin 3) : (roots i)^2=(PadicTwo.independentRadicand i : GenusField) := by
  rw [roots_sq,radicands,map_intCast]

theorem roots_ne_zero (i : Fin 3) : roots i≠0 := by
  intro h
  have hh := roots_sq i
  rw [h,zero_pow (by decide : 2≠0)] at hh
  exact (map_ne_zero (algebraMap ℚ_[2] GenusField)).mpr (radicands_ne_zero i) hh.symm

def signHom : Gal(GenusField/ℚ_[2]) →* Multiplicative (Fin 3 → ZMod 2) :=
  rootSignHom radicands roots roots_sq roots_ne_zero

theorem signHom_bijective : Function.Bijective signHom := by
  refine ⟨rootSignHom_injective radicands roots roots_sq roots_ne_zero genusTower.generated,?_⟩
  exact rootSignHom_surjective radicands roots roots_sq roots_ne_zero PadicTwo.independent_products

def signEquiv : Gal(GenusField/ℚ_[2]) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  MulEquiv.ofBijective signHom signHom_bijective

def signAutomorphism (v : Fin 3 → ZMod 2) : Gal(GenusField/ℚ_[2]) :=
  signEquiv.symm (Multiplicative.ofAdd v)

theorem signAutomorphism_roots (v : Fin 3 → ZMod 2) (i : Fin 3) :
    signAutomorphism v (roots i)=binarySign (v i)*roots i := by
  have h := rootCharacter_action radicands roots roots_sq (signAutomorphism v) i
  have he := congrArg (fun x : Multiplicative (Fin 3 → ZMod 2) => x.toAdd i)
    (signEquiv.apply_symm_apply (Multiplicative.ofAdd v))
  change rootCharacter roots (signAutomorphism v) i=v i at he
  rw [he] at h
  exact h

theorem signAutomorphism_involutive (v : Fin 3 → ZMod 2) :
    Function.Involutive (signAutomorphism v) := by
  have he : signAutomorphism v*signAutomorphism v=1 := by
    apply signEquiv.injective
    rw [map_mul,map_one,show signEquiv (signAutomorphism v)=Multiplicative.ofAdd v from
      signEquiv.apply_symm_apply _]
    apply Multiplicative.toAdd.injective
    funext i
    have h : ∀ x : ZMod 2,x+x=0 := by decide
    exact h (v i)
  intro x
  exact congrArg (fun σ : Gal(GenusField/ℚ_[2]) => σ x) he

end UnitDistance.PadicTwoGenus
