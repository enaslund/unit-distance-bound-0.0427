module

public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Cohomology.RelativeNakayama
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Presentations.Profinite

@[expose] public section
set_option backward.privateInPublic true


/-! Replacing one actual normal relator using an invariant binary character. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.RelativeRelatorReplacement
open ProCGroups ProCGroups.ProC ProCGroups.Presentations ClassFieldTower.ProP
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {F : Type*} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- Invariant continuous characters agree everywhere when they agree on a
set that normally generates the actual closed subgroup. -/
theorem invariant_character_ext (R : ClosedSubgroup F) [R.Normal]
    (S : Set F) (hgen : closedNormalClosure S=(R : Subgroup F))
    (χ ψ : R →ₜ* Multiplicative (ZMod 2))
    (hχ : ∀f r,χ (MulAut.conjNormal f r)=χ r)
    (hψ : ∀f r,ψ (MulAut.conjNormal f r)=ψ r)
    (hS : ∀r : R,(r : F)∈S → χ r=ψ r) : χ=ψ := by
  let N : Subgroup F := (MonoidHom.eqLocus χ.toMonoidHom ψ.toMonoidHom).map (R : Subgroup F).subtype
  letI : N.Normal := by
    refine ⟨?_⟩
    intro x hx f
    obtain ⟨r,hr,rfl⟩ := hx
    refine ⟨MulAut.conjNormal f r,?_,rfl⟩
    change χ (MulAut.conjNormal f r)=ψ (MulAut.conjNormal f r)
    rw [hχ,hψ]
    exact hr
  have hc : IsClosed (N : Set F) :=
    R.isClosed'.isClosedMap_subtype_val _ (isClosed_eq χ.continuous ψ.continuous)
  have hle : (R : Subgroup F)≤N := by
    rw [←hgen]
    apply closedNormalClosure_le_closed_normal hc
    intro x hx
    have hxR : x∈R := by
      change x∈(R : Subgroup F)
      rw [←hgen]
      exact subset_closedNormalClosure S hx
    exact ⟨⟨x,hxR⟩,hS ⟨x,hxR⟩ hx,rfl⟩
  ext r
  obtain ⟨u,hu,huval⟩ := hle r.property
  have he : u=r := Subtype.ext huval
  subst u
  exact hu

/-- A genuine new relator can replace the distinguished old one whenever
an invariant binary character detects both and kills all remaining relators.
The conclusion follows from relative pro-two Nakayama, with no additional
presentation or relation-rank assumption. -/
theorem closedNormalClosure_replace
    (hF : HasPGroupOpenNormalBasis 2 F) (R : ClosedSubgroup F) [R.Normal]
    (s r : R) (T : Set F)
    (hgen : closedNormalClosure (insert (s : F) T)=(R : Subgroup F))
    (χ : R →ₜ* Multiplicative (ZMod 2))
    (hχinv : ∀f u,χ (MulAut.conjNormal f u)=χ u)
    (hχs : χ s≠1) (hχT : ∀u : R,(u : F)∈T → χ u=1) (hχr : χ r≠1) :
    closedNormalClosure (insert (r : F) T)=(R : Subgroup F) := by
  classical
  let K : ClosedSubgroup F :=
    ⟨closedNormalClosure (insert (r : F) T),closedNormalClosure_isClosed _⟩
  letI : K.Normal := inferInstanceAs (closedNormalClosure (insert (r : F) T)).Normal
  have hTR : T⊆R := by
    intro x hx
    change x∈(R : Subgroup F)
    rw [←hgen]
    exact subset_closedNormalClosure _ (Set.mem_insert_of_mem _ hx)
  have hKR : K≤R := by
    apply closedNormalClosure_le_closed_normal R.isClosed'
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact r.property
    · exact hTR hx
  by_contra hne
  have hstrict : K<R := lt_of_le_of_ne hKR (by
    intro h
    exact hne (congrArg (fun L : ClosedSubgroup F => (L : Subgroup F)) h))
  obtain ⟨ψ,hψne,hψkill,hψinv⟩ := relativeNakayama_character hF K R hstrict
  have hψr : ψ r=1 := by
    have hrK : (r : F)∈K := subset_closedNormalClosure _ (Set.mem_insert _ _)
    exact hψkill ⟨r,hrK⟩
  have hψT (u : R) (hu : (u : F)∈T) : ψ u=1 := by
    have huK : (u : F)∈K := subset_closedNormalClosure _ (Set.mem_insert_of_mem _ hu)
    exact hψkill ⟨u,huK⟩
  have hψs : ψ s≠1 := by
    intro hs
    apply hψne
    apply invariant_character_ext R _ hgen ψ 1 hψinv (by intros; rfl)
    intro u hu
    rcases hu with hu | hu
    · have he : u=s := Subtype.ext hu
      subst u
      exact hs
    · exact hψT u hu
  have he : χ s=ψ s := by
    have hh : ∀a b : Multiplicative (ZMod 2),a≠1 → b≠1 → a=b := by decide +kernel
    exact hh _ _ hχs hψs
  have hχψ : χ=ψ := by
    apply invariant_character_ext R _ hgen χ ψ hχinv hψinv
    intro u hu
    rcases hu with hu | hu
    · have heu : u=s := Subtype.ext hu
      subst u
      exact he
    · rw [hχT u hu,hψT u hu]
  exact hχr ((congrArg (fun f : R →ₜ* Multiplicative (ZMod 2) => f r) hχψ).trans hψr)

end UnitDistance.RelativeRelatorReplacement
