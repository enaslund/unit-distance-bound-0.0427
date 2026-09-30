module

public import UnitDistance.QuadraticRadicalPresentation
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

@[expose] public section
set_option backward.privateInPublic true


/-! The actual norm obstruction associated to a cyclic quartic automorphism. -/
noncomputable section
namespace UnitDistance.CyclicQuartic
open IntermediateField KummerInvariant
variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

/-- An automorphism of order four supplies a nonzero vector anti-invariant
under its square, and a quotient with norm minus one. -/
theorem antiInvariant_quotient (σ : Gal(L/F)) (h4 : σ^4=1) (h2 : σ^2≠1) :
    ∃ a γ : L,a≠0 ∧ (σ^2) a= -a ∧ (σ^2) γ=γ ∧ γ*σ γ= -1 := by
  have hex : ∃ t : L,(σ^2) t≠t := by
    by_contra! h
    apply h2
    exact AlgEquiv.ext h
  obtain ⟨t,ht⟩ := hex
  let a := t-(σ^2) t
  have ha : a≠0 := sub_ne_zero.mpr ht.symm
  have hsq : (σ^2)^2=1 := by simpa only [← pow_mul] using h4
  have haa : (σ^2) a= -a := by
    dsimp [a]
    rw [map_sub,← AlgEquiv.mul_apply,← pow_two,hsq,AlgEquiv.one_apply]
    ring
  have hsaa : (σ^2) (σ a)= -σ a := by
    change σ ((σ^2) a)= -σ a
    rw [haa,map_neg]
  let γ := σ a/a
  have hγ : (σ^2) γ=γ := by
    dsimp [γ]
    rw [map_div₀,hsaa,haa]
    simp
  have hn : γ*σ γ= -1 := by
    dsimp [γ]
    rw [map_div₀]
    change σ a/a*((σ^2) a/σ a)= -1
    rw [haa]
    have hsa : σ a≠0 := (map_ne_zero σ).mpr ha
    field_simp
  exact ⟨a,γ,ha,haa,hγ,hn⟩

/-- Fixing a generator of a cyclic subgroup fixes its whole fixed field condition. -/
theorem mem_fixedField_zpowers (τ : Gal(L/F)) (a : L) (ha : τ a=a) :
    a∈IntermediateField.fixedField (Subgroup.zpowers τ) := by
  apply (IntermediateField.mem_fixedField_iff _ a).mpr
  have hle : Subgroup.zpowers τ≤MulAction.stabilizer Gal(L/F) a :=
    Subgroup.zpowers_le.mpr ha
  intro g hg
  exact hle hg

/-- For an order-four automorphism in a degree-four Galois field, the fixed
field of its square has actual relative degree two. -/
theorem fixed_square_degree (hd : Module.finrank F L=4) (σ : Gal(L/F))
    (hσ : orderOf σ=4) :
    Module.finrank F (IntermediateField.fixedField (Subgroup.zpowers (σ^2)))=2 := by
  have hc : Nat.card (Subgroup.zpowers (σ^2))=2 := by
    rw [Nat.card_zpowers,orderOf_pow,hσ]
    norm_num
  have he := IntermediateField.finrank_fixedField_eq_card (F:=F) (E:=L)
    (Subgroup.zpowers (σ^2))
  have ht := Module.finrank_mul_finrank F
    (IntermediateField.fixedField (Subgroup.zpowers (σ^2))) L
  rw [hd,he,hc] at ht
  omega

/-- The quadratic norm is multiplication by the actual conjugate. -/
theorem norm_eq_mul_conjugate [Fact (Nonsquare (-1 : F))]
    (i : L) (hi : i^2= -1) (hd : Module.finrank F L=2)
    (σ : Gal(L/F)) (hσ : σ i= -i) (z : L) :
    algebraMap F L (Algebra.norm F z)=z*σ z := by
  let e := QuadraticRadical.equiv (-1 : F) i (by simpa using hi) hd
  let t := e.symm z
  have hz : z=algebraMap F L t.re+algebraMap F L t.im*i := by
    have h := e.apply_symm_apply z
    change t.re • (1 : L)+t.im • i=z at h
    simpa only [Algebra.smul_def,mul_one] using h.symm
  have hn : Algebra.norm F z=t.re^2+t.im^2 := by
    have h := Algebra.norm_eq_of_algEquiv e t
    rw [show e t=z from e.apply_symm_apply z] at h
    rw [h,Algebra.norm_apply]
    change (DistribSMul.toLinearMap F (Extension (-1 : F)) t).det=_
    rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
    simp [QuadraticAlgebra.norm]
    ring
  rw [hn,map_add,map_pow,map_pow]
  calc
    (algebraMap F L t.re)^2+(algebraMap F L t.im)^2 =
        (algebraMap F L t.re+algebraMap F L t.im*i)*
        (algebraMap F L t.re+algebraMap F L t.im*(-i)) := by
      linear_combination (algebraMap F L t.im)^2*hi
    _ = z*σ z := by
      conv_rhs => rw [hz,map_add,map_mul,σ.commutes,σ.commutes,hσ]


/-- An actual cyclic quartic field containing a nonsquare root of minus one
has an actual quadratic subfield in which minus one is a norm. -/
theorem exists_quadratic_norm_neg_one [IsCyclic Gal(L/F)] [Fact (Nonsquare (-1 : F))]
    (hd : Module.finrank F L=4) (i : L) (hi : i^2= -1) :
    ∃ (E : IntermediateField F L) (iE : E), iE^2= -1 ∧ Module.finrank F E=2 ∧
      ∃ z : E,Algebra.norm F z= -1 := by
  obtain ⟨σ,hgen⟩ := IsCyclic.exists_generator (α:=Gal(L/F))
  have ho : orderOf σ=4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen,IsGalois.card_aut_eq_finrank,hd]
  have h4 : σ^4=1 := by rw [← ho]; exact pow_orderOf_eq_one σ
  have h2 : σ^2≠1 := by
    intro h
    have hh := orderOf_dvd_of_pow_eq_one h
    rw [ho] at hh
    norm_num at hh
  have hs : σ i= -i := by
    have he : (σ i)^2=i^2 := by rw [← map_pow,hi,map_neg,map_one]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
    · have hmem := mem_fixedField_zpowers σ i h
      have hall : ∀ τ : Gal(L/F),τ i=i := fun τ =>
        (IntermediateField.mem_fixedField_iff _ i).mp hmem τ (hgen τ)
      obtain ⟨r,hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed i).mpr hall
      exfalso
      apply (Fact.out : Nonsquare (-1 : F)) r
      apply (algebraMap F L).injective
      rw [map_pow,hr,map_neg,map_one,hi]
    · exact h
  let H := Subgroup.zpowers (σ^2)
  let E := IntermediateField.fixedField H
  have hE : Module.finrank F E=2 := fixed_square_degree hd σ ho
  have hiτ : (σ^2) i=i := by rw [pow_two,AlgEquiv.mul_apply,hs,map_neg,hs,neg_neg]
  let iE : E := ⟨i,mem_fixedField_zpowers (σ^2) i hiτ⟩
  have hiE : iE^2= -1 := by apply Subtype.ext; exact hi
  obtain ⟨a,γ,ha,haa,hγ,hn⟩ := antiInvariant_quotient σ h4 h2
  let z : E := ⟨γ,mem_fixedField_zpowers (σ^2) γ hγ⟩
  haveI : IsAbelianGalois F L := IsAbelianGalois.of_isCyclic F L
  let τ : Gal(E/F) := σ.restrictNormal E
  have hτ : τ iE= -iE := by
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ E iE).trans hs
  refine ⟨E,iE,hiE,hE,z,?_⟩
  have hnorm := norm_eq_mul_conjugate iE hiE hE τ hτ z
  apply (algebraMap F L).injective
  rw [IsScalarTower.algebraMap_apply F E L,map_neg,map_one]
  rw [hnorm,map_mul]
  change γ*(τ z : L)= -1
  have hzτ : (τ z : L)=σ γ := AlgEquiv.restrictNormal_commutes σ E z
  rw [hzτ]
  exact hn


end UnitDistance.CyclicQuartic
