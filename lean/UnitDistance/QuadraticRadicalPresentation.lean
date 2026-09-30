module

public import UnitDistance.KummerInvariantRadicand

@[expose] public section
set_option backward.privateInPublic true


/-! A displayed nonsquare radical and actual relative degree two identify
an actual field with the corresponding quadratic algebra. -/
noncomputable section
namespace UnitDistance.QuadraticRadical
open QuadraticAlgebra KummerInvariant
variable {F K : Type*} [Field F] [CharZero F] [Field K] [Algebra F K]

def hom (a : F) (r : K) (hr : r^2=algebraMap F K a) : Extension a →ₐ[F] K :=
  QuadraticAlgebra.lift ⟨r,by simpa [pow_two,Algebra.smul_def] using hr⟩

def equiv (a : F) [Fact (Nonsquare a)] (r : K)
    (hr : r^2=algebraMap F K a) (hd : Module.finrank F K=2) : Extension a ≃ₐ[F] K := by
  let f := hom a r hr
  haveI : Module.Finite F K := FiniteDimensional.of_finrank_pos (by omega)
  have hdim : Module.finrank F (LinearMap.range f.toLinearMap)=Module.finrank F K := by
    calc
      Module.finrank F (LinearMap.range f.toLinearMap)=Module.finrank F (Extension a) :=
        (LinearEquiv.ofInjective f.toLinearMap f.injective).finrank_eq.symm
      _ = 2 := QuadraticAlgebra.finrank_eq_two _ _
      _ = Module.finrank F K := hd.symm
  exact AlgEquiv.ofBijective f ⟨f.injective,
    LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hdim)⟩

@[simp] theorem equiv_root (a : F) [Fact (Nonsquare a)] (r : K)
    (hr : r^2=algebraMap F K a) (hd : Module.finrank F K=2) :
    equiv a r hr hd omega=r := by
  change (omega : Extension a).re • (1 : K)+(omega : Extension a).im • r=r
  simp

end UnitDistance.QuadraticRadical
