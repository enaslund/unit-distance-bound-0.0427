module

public import UnitDistance.RelativeUnitsRegulator

@[expose] public section
set_option backward.privateInPublic true


/-! A literal enumeration of actual relative units by torsion and their
actual logarithmic lattice. The chosen section is a set map; no splitting
of the integral unit lattice or coordinate independence is assumed. -/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units
open scoped Classical
namespace UnitDistance.RelativeUnits
variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- Choose an actual relative unit above each point of its actual log image. -/
def differenceRepresentative (ι : K ≃ₐ[F] K) (l : differenceLattice ι) :
    Additive (normOneUnits (F := F) (K := K)) := Classical.choose l.prop

@[simp] theorem differenceRepresentative_log (ι : K ≃ₐ[F] K)
    (l : differenceLattice ι) :
    relativeDifferenceLog ι (differenceRepresentative ι l) = l.val :=
  Classical.choose_spec l.prop

/-- Multiply a chosen logarithmic representative by an actual root of unity. -/
def enumerateRelativeUnit (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) (p : torsion K × differenceLattice ι) :
    Additive (normOneUnits (F := F) (K := K)) :=
  ((differenceLogKernelEquivTorsion ι hι hb).symm p.1).val + differenceRepresentative ι p.2

@[simp] theorem enumerateRelativeUnit_log (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) (p : torsion K × differenceLattice ι) :
    relativeDifferenceLog ι (enumerateRelativeUnit ι hι hb p) = p.2.val := by
  rw [enumerateRelativeUnit, map_add]
  have hz : relativeDifferenceLog ι ((differenceLogKernelEquivTorsion ι hι hb).symm p.1).val = 0 :=
    ((differenceLogKernelEquivTorsion ι hι hb).symm p.1).prop
  rw [hz, zero_add, differenceRepresentative_log]

theorem enumerateRelativeUnit_injective (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) : Function.Injective (enumerateRelativeUnit ι hι hb) := by
  rintro ⟨τ, l⟩ ⟨σ, m⟩ he
  have hl : l = m := by
    apply Subtype.ext
    have h := congrArg (relativeDifferenceLog ι) he
    simpa only [enumerateRelativeUnit_log] using h
  subst m
  have ht : τ = σ := by
    apply (differenceLogKernelEquivTorsion ι hι hb).symm.injective
    apply Subtype.ext
    exact add_right_cancel he
  subst σ
  rfl

theorem enumerateRelativeUnit_surjective (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) : Function.Surjective (enumerateRelativeUnit ι hι hb) := by
  intro u
  let l : differenceLattice ι := ⟨relativeDifferenceLog ι u, u, rfl⟩
  let k : (relativeDifferenceLog ι).toIntLinearMap.ker :=
    ⟨u-differenceRepresentative ι l, by
      change relativeDifferenceLog ι (u-differenceRepresentative ι l) = 0
      rw [map_sub, differenceRepresentative_log]
      exact sub_self _⟩
  refine ⟨((differenceLogKernelEquivTorsion ι hι hb) k, l), ?_⟩
  rw [enumerateRelativeUnit, Equiv.symm_apply_apply]
  exact sub_add_cancel u (differenceRepresentative ι l)

/-- Actual relative units are enumerated once each; torsion occurs exactly once
per actual log-lattice point. This equivalence asserts no group splitting. -/
def relativeUnitEquiv (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    torsion K × differenceLattice ι ≃ Additive (normOneUnits (F := F) (K := K)) :=
  Equiv.ofBijective (enumerateRelativeUnit ι hι hb)
    ⟨enumerateRelativeUnit_injective ι hι hb, enumerateRelativeUnit_surjective ι hι hb⟩

@[simp] theorem relativeUnitEquiv_log (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) (p : torsion K × differenceLattice ι) :
    relativeDifferenceLog ι (relativeUnitEquiv ι hι hb p) = p.2.val :=
  enumerateRelativeUnit_log ι hι hb p

end UnitDistance.RelativeUnits
