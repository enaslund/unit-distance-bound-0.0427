module

public import UnitDistance.EuclideanIdealDual
public import UnitDistance.RelativeUnitsPlaces
public import UnitDistance.GeometryProjection

@[expose] public section
set_option backward.privateInPublic true


/-! Actual fractional-ideal lattice points project injectively to the plane.
The real place in the base supplies the compact complex embedding, so every
relative-norm-one displacement is an ordinary Euclidean unit vector. -/

noncomputable section
open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors Classical
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K]

theorem embedding_injective : Function.Injective (embedding K) :=
  (coordinates K).symm.injective.comp (mixedEmbedding_injective K)

@[simp] theorem embedding_add (x y : K) :
    embedding K (x+y) = embedding K x+embedding K y := by
  simp only [embedding, map_add]

/-- The actual fractional ideal and its Euclidean lattice are additively equivalent. -/
def idealLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (I : FractionalIdeal (𝓞 K)⁰ K) ≃+ lattice K I :=
  { Equiv.ofBijective (fun x : (I : FractionalIdeal (𝓞 K)⁰ K) =>
      (⟨embedding K x.val,
        (mem_lattice_iff K I _).mpr ⟨x.val, x.prop, rfl⟩⟩ : lattice K I))
      (by
        constructor
        · intro x y h
          exact Subtype.ext (embedding_injective K (congrArg Subtype.val h))
        · intro y
          obtain ⟨x, hx, hxy⟩ := (mem_lattice_iff K I y.val).mp y.prop
          exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩) with
    map_add' x y := Subtype.ext (embedding_add K x.val y.val) }

@[simp] theorem idealLatticeEquiv_coe (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (idealLatticeEquiv K I x : Space K) = embedding K x.val := rfl

/-- Projection uses the actual field element represented by a lattice point. -/
def idealPlaneProjection (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (σ : K →+* ℂ) : lattice K I →+ ℂ where
  toFun v := σ ((idealLatticeEquiv K I).symm v).val
  map_zero' := by simp
  map_add' v w := by simp

theorem idealPlaneProjection_injective (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (σ : K →+* ℂ) : Function.Injective (idealPlaneProjection K I σ) := by
  intro x y h
  apply (idealLatticeEquiv K I).symm.injective
  apply Subtype.ext
  exact σ.injective h

@[simp] theorem idealPlaneProjection_embedding (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (σ : K →+* ℂ) (x : K) (hx : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    idealPlaneProjection K I σ
      ⟨embedding K x, (mem_lattice_iff K I _).mpr ⟨x, hx, rfl⟩⟩ = σ x := by
  change σ ((idealLatticeEquiv K I).symm (idealLatticeEquiv K I ⟨x, hx⟩)).val = σ x
  rw [AddEquiv.symm_apply_apply]

end UnitDistance.EuclideanIdeal

namespace UnitDistance.RelativeUnits
variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The field/signature assumptions themselves give an injective additive
plane projection sending every actual norm-one ideal displacement to a unit vector. -/
theorem exists_idealPlaneProjection (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ φ : EuclideanIdeal.lattice K I →+ ℂ, Function.Injective φ ∧
      ∀ (x : K) (hx : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)), Algebra.norm F x = 1 →
        ‖φ ⟨EuclideanIdeal.embedding K x,
          (EuclideanIdeal.mem_lattice_iff K I _).mpr ⟨x, hx, rfl⟩⟩‖ = 1 := by
  obtain ⟨ρ, σ, hbase, hconj⟩ := exists_complexifying_embeddings ι hι hb
  refine ⟨EuclideanIdeal.idealPlaneProjection K I σ,
    EuclideanIdeal.idealPlaneProjection_injective K I σ, ?_⟩
  intro x hx hn
  rw [EuclideanIdeal.idealPlaneProjection_embedding K I σ x hx]
  apply complex_norm_of_relative_norm_one σ ι.toRingHom hconj
  change x*ι x = 1
  rw [← norm_eq_mul_involution ι hι, hn, map_one]

end UnitDistance.RelativeUnits
