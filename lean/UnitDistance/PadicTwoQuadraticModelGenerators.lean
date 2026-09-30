module

public import UnitDistance.PadicTwoQuadraticCharacters
public import UnitDistance.LocalQuadraticModel

@[expose] public section
set_option backward.privateInPublic true


/-! Actual local genus lifts realize the independently defined quadratic model. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.PadicTwoQuadratic
open Multiquadratic PadicTwoGenus PadicTwoNormCatalog
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem genusVector_surjective : Function.Surjective genusVector := by
  intro v
  obtain ⟨σ,hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F:=ℚ_[2]) (K₁:=E) (E:=QuadraticField) (signAutomorphism v)
  refine ⟨σ,?_⟩
  change (signEquiv (σ.restrictNormal E)).toAdd=v
  rw [show σ.restrictNormal E=signAutomorphism v from hσ]
  exact congrArg Multiplicative.toAdd (signEquiv.apply_symm_apply (Multiplicative.ofAdd v))

def basisLift (i : Fin 3) : G := (genusVector_surjective (Pi.single i 1)).choose

theorem genusVector_basisLift (i : Fin 3) : genusVector (basisLift i)=Pi.single i 1 :=
  (genusVector_surjective (Pi.single i 1)).choose_spec

theorem quadratic_aut_ext_roots {σ τ : G}
    (hbase : ∀ a : E,σ (algebraMap E QuadraticField a)=τ (algebraMap E QuadraticField a))
    (hroots : ∀ j,σ (quadraticRoot j)=τ (quadraticRoot j)) : σ=τ := by
  apply quadraticTower.aut_ext _ _ hbase
  rintro x ⟨j,hj,hx⟩
  have hs : x^2=(quadraticRoot j)^2 := hx.trans (quadraticRoot_sq j).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
  · simpa only [hs] using hroots j
  · simpa only [hs,map_neg] using congrArg Neg.neg (hroots j)

theorem square_fixes_genus (σ : G) (a : E) :
    (σ^2) (algebraMap E QuadraticField a)=algebraMap E QuadraticField a :=
  quadraticTower.aut_square_fixes_base every_genus_automorphism_involutive σ a

theorem commutator_fixes_genus (σ τ : G) (a : E) :
    (σ⁻¹*τ⁻¹*σ*τ) (algebraMap E QuadraticField a)=algebraMap E QuadraticField a := by
  rw [commutator_eq_three_squares]
  simp only [AlgEquiv.mul_apply,square_fixes_genus]

theorem cocycle_diagonal_certificate (i : Fin 3) (k : Fin 5) :
    LocalQuadraticModel.cocycle (Pi.single i 1) (Pi.single i 1) k=
      form k (Pi.single i 1) := by
  have h : ∀ (i : Fin 3) (k : Fin 5),
    LocalQuadraticModel.cocycle (Pi.single i 1) (Pi.single i 1) k=
      form k (Pi.single i 1) := by decide +kernel
  exact h i k

theorem cocycle_polar_certificate (i j : Fin 3) (k : Fin 5) :
    LocalQuadraticModel.swapCoordinate i j k=
      form k (Pi.single i 1+Pi.single j 1)+form k (Pi.single i 1)+form k (Pi.single j 1) := by
  have h : ∀ (i j : Fin 3) (k : Fin 5),
    LocalQuadraticModel.swapCoordinate i j k=
      form k (Pi.single i 1+Pi.single j 1)+form k (Pi.single i 1)+form k (Pi.single j 1) := by
    decide +kernel
  exact h i j k

theorem basisLift_square (i : Fin 3) : basisLift i^2=centralSignHom
    (Multiplicative.ofAdd (LocalQuadraticModel.cocycle (Pi.single i 1) (Pi.single i 1))) := by
  apply quadratic_aut_ext_roots
  · intro a
    rw [centralSignHom_fixes_genus,square_fixes_genus]
  · intro k
    rw [square_action _ k _ (quadraticRoot_sq k),centralSignHom_action,
      genusVector_basisLift]
    exact congrArg
      (fun t => binarySign (E:=QuadraticField) t*quadraticRoot k)
      (cocycle_diagonal_certificate i k).symm

theorem basisLift_commutator (i j : Fin 3) :
    (basisLift i)⁻¹*(basisLift j)⁻¹*basisLift i*basisLift j=
      centralSignHom (Multiplicative.ofAdd (LocalQuadraticModel.swapCoordinate i j)) := by
  apply quadratic_aut_ext_roots
  · intro a
    rw [centralSignHom_fixes_genus,commutator_fixes_genus]
  · intro k
    rw [commutator_action _ _ k _ (quadraticRoot_sq k),centralSignHom_action,
      genusVector_basisLift,genusVector_basisLift]
    exact congrArg
      (fun t => binarySign (E:=QuadraticField) t*quadraticRoot k)
      (cocycle_polar_certificate i j k).symm

theorem basisLift_swap (i j : Fin 3) : basisLift i*basisLift j=
    centralSignHom (Multiplicative.ofAdd (LocalQuadraticModel.swapCoordinate i j))*basisLift j*basisLift i := by
  calc
    basisLift i*basisLift j=(basisLift j*basisLift i)*
      ((basisLift i)⁻¹*(basisLift j)⁻¹*basisLift i*basisLift j) := by group
    _ = _ := by
      rw [basisLift_commutator,(centralSignHom_central _ (basisLift j*basisLift i)).symm.eq]
      group

end UnitDistance.PadicTwoQuadratic
