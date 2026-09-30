module

public import UnitDistance.QuadraticSignLift
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Independent actual radical products force surjectivity of their actual
Galois sign map. This uses the finite Galois fixed-field theorem and ordinary
linear duality; no Kummer rank is assumed. -/
noncomputable section
namespace UnitDistance.Multiquadratic
open scoped BigOperators
variable {F K : Type*} [Field F] [CharZero F] [Field K] [CharZero K]
  [Algebra F K] [IsGalois F K] [Module.Finite F K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem binarySign_mul_val (a b : ZMod 2) :
    binarySign (E := K) (a*b)=(binarySign a)^b.val := by
  have h : ∀ a b : ZMod 2,binarySignInteger (a*b)=binarySignInteger a ^ b.val := by decide +kernel
  unfold binarySign
  exact_mod_cast h a b

/-- If no nonempty product of the radicands is square, every sign vector occurs. -/
theorem signHom_surjective_of_products
    (r : ι → K) (d : ι → F) (hr : ∀ i,(r i)^2=algebraMap F K (d i))
    (q : Gal(K/F) →* Multiplicative (ι → ZMod 2))
    (hq : ∀ σ i,σ (r i)=binarySign ((q σ).toAdd i)*r i)
    (hind : ∀ w : ι → ZMod 2,IsSquare (∏ i,d i ^ (w i).val) → w=0) :
    Function.Surjective q := by
  let S : Submodule (ZMod 2) (ι → ZMod 2) := {
    carrier := {v | ∃ σ,(q σ).toAdd=v}
    zero_mem' := ⟨1,by simp⟩
    add_mem' := by
      rintro v w ⟨σ,rfl⟩ ⟨τ,rfl⟩
      exact ⟨σ*τ,by rw [map_mul]; rfl⟩
    smul_mem' := by
      rintro t v ⟨σ,rfl⟩
      have ht : t=0 ∨ t=1 := (by decide : ∀ t : ZMod 2,t=0 ∨ t=1) t
      rcases ht with rfl | rfl
      · exact ⟨1,by simp⟩
      · exact ⟨σ,by simp⟩ }
  have htop : S=⊤ := by
    apply (Submodule.dualAnnihilator_eq_bot_iff).mp
    apply le_antisymm _ bot_le
    intro f hf
    let w : ι → ZMod 2 := fun i => f (Pi.single i 1)
    have hfapply (v : ι → ZMod 2) : f v=∑ i,v i*w i := by
      have he : v=∑ i,v i • Pi.single i 1 := by
        ext j
        simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp
        · intro i hi hij
          simp [Pi.single_apply,hij,Ne.symm hij]
        · simp
      conv_lhs => rw [he]
      simp [w]
    have hann (σ : Gal(K/F)) : ∑ i,(q σ).toAdd i*w i=0 := by
      rw [← hfapply]
      exact (Submodule.mem_dualAnnihilator _).mp hf _ ⟨σ,rfl⟩
    let R : K := ∏ i,r i ^ (w i).val
    have hfixed : ∀ σ : Gal(K/F),σ R=R := by
      intro σ
      change σ (∏ i,r i ^ (w i).val)=_
      simp only [map_prod,map_pow,hq,mul_pow,Finset.prod_mul_distrib]
      have hs : (∏ i,(binarySign ((q σ).toAdd i) : K) ^ (w i).val)=1 := by
        simp_rw [← binarySign_mul_val]
        rw [← binarySign_sum, hann σ,binarySign_zero]
      rw [hs,one_mul]
    obtain ⟨a,ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed R).mpr hfixed
    have hs : IsSquare (∏ i,d i ^ (w i).val) := by
      refine ⟨a,?_⟩
      apply (algebraMap F K).injective
      rw [map_mul,ha]
      change algebraMap F K (∏ i,d i ^ (w i).val)=R*R
      rw [← pow_two]
      dsimp only [R]
      rw [← Finset.prod_pow]
      simp only [map_prod,map_pow,← pow_mul]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Nat.mul_comm, pow_mul,hr i]
    have hw : w=0 := hind w hs
    apply LinearMap.ext
    intro v
    rw [hfapply,hw]
    simp
  intro v
  have hv : v.toAdd∈S := htop ▸ Submodule.mem_top
  obtain ⟨σ,hσ⟩ := hv
  exact ⟨σ,Multiplicative.toAdd.injective hσ⟩

end UnitDistance.Multiquadratic
