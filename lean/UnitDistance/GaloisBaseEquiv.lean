module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Changing a base field through a surjective algebra embedding preserves
actual finite Galois groups, with the automorphisms acting identically. -/
noncomputable section
namespace UnitDistance.GaloisBaseEquiv
variable (F K L : Type*) [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]

/-- The actual Galois groups agree when the two base fields have the same image. -/
def autEquiv (h : Function.Surjective (algebraMap F K)) : Gal(L/F) ≃* Gal(L/K) where
  toFun σ :=
    { σ.toRingEquiv with
      commutes' := fun k ↦ by
        obtain ⟨f,rfl⟩ := h k
        rw [← IsScalarTower.algebraMap_apply F K L]
        exact σ.commutes f }
  invFun τ := τ.restrictScalars F
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

@[simp] theorem autEquiv_apply (h : Function.Surjective (algebraMap F K))
    (σ : Gal(L/F)) (x : L) : autEquiv F K L h σ x=σ x := rfl

@[simp] theorem autEquiv_symm_apply (h : Function.Surjective (algebraMap F K))
    (τ : Gal(L/K)) (x : L) : (autEquiv F K L h).symm τ x=τ x := rfl

omit [Algebra K L] [Algebra F L] [IsScalarTower F K L] in
theorem baseFinite (h : Function.Surjective (algebraMap F K)) : Module.Finite F K :=
  Module.Finite.of_surjective (Algebra.linearMap F K) h

/-- Finiteness transfers without a degree hypothesis beyond the true base isomorphism. -/
theorem finite (h : Function.Surjective (algebraMap F K)) [Module.Finite K L] :
    Module.Finite F L := by
  letI := baseFinite F K h
  exact Module.Finite.trans K L

/-- Normality transfers through the actual isomorphism of base fields. -/
theorem normal (h : Function.Surjective (algebraMap F K)) [Normal K L] : Normal F L := by
  let e : F ≃+* K := RingEquiv.ofBijective (algebraMap F K) ⟨(algebraMap F K).injective,h⟩
  apply Normal.of_equiv_equiv (F:=K) (E:=L) (f:=e.symm) (g:=RingEquiv.refl L)
  ext k
  change algebraMap F L (e.symm k)=algebraMap K L k
  rw [IsScalarTower.algebraMap_apply F K L]
  change algebraMap K L (e (e.symm k))=algebraMap K L k
  rw [e.apply_symm_apply]

/-- In characteristic zero, the actual finite Galois property transfers as well. -/
theorem galois (h : Function.Surjective (algebraMap F K))
    [CharZero F] [Module.Finite K L] [IsGalois K L] : IsGalois F L := by
  letI := finite F K L h
  exact { to_normal := normal F K L h }

end UnitDistance.GaloisBaseEquiv
