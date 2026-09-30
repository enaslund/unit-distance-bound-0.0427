module

public import UnitDistance.Sqrt241.GroupData.MagnusConjugacy
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.FreeProC.Basic
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Presentations.Profinite
public import UnitDistance.GroupAugmentationWordDegrees
public import Mathlib.Algebra.CharP.Two

@[expose] public section
set_option backward.privateInPublic true


/-!
# The truncated Magnus detector of a free pro-2 group on `n` generators

Copy of `TruncatedMagnusFree`, `TruncatedMagnusWords` (generic word
coordinates) and the genus agreement of `RetainedMagnusGenus`, for `n`
generators and certificate data `C : CutData n m a b`. The finite Magnus
group is a discrete 2-group, so the free universal property gives a
continuous detector; its cut quotient kills every relator with the prescribed
quadratic initial (with the relator's own cubic tail), every central element
killed by the third detector, and every element of augmentation degree four.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Magnus
open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations
open _root_.UnitDistance.Sqrt241.Magnus.Group
open scoped CharTwo
variable {n : ℕ}

instance : TopologicalSpace (Group n (ZMod 2)) := ⊥
instance : DiscreteTopology (Group n (ZMod 2)) := ⟨rfl⟩
instance : IsTopologicalGroup (Group n (ZMod 2)) := by infer_instance

theorem hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 (Group n (ZMod 2)) := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance,(binaryGroup_isTwoGroup n).of_surjective
    (QuotientGroup.mk' (U : Subgroup (Group n (ZMod 2))))
    (QuotientGroup.mk'_surjective (U : Subgroup (Group n (ZMod 2))))⟩

/-! ### Word coordinates in the Magnus group over `F₂` -/

theorem pow_four (g : Group n F) : g^4 = 1 := by
  rw [show (4 : ℕ) = 2*2 by decide,pow_mul]
  ext <;> simp [pow_two]

@[simp] theorem square_first (g : Group n F) : (g^2).first = 0 := by
  ext i
  simp [pow_two]

theorem square_second (g : Group n F) : (g^2).second = squareTensor g.first := by
  ext i j
  simp [pow_two,squareTensor]

def commutator (g h : Group n F) : Group n F := g⁻¹*h⁻¹*g*h

@[simp] theorem commutator_first (g h : Group n F) : (commutator g h).first = 0 := by
  simp [commutator]

theorem commutator_second (g h : Group n F) :
    (commutator g h).second = quadraticBracket g.first h.first := by
  ext i j
  simpa [commutator,quadraticBracket] using Group.commutator_second g⁻¹ h⁻¹ i j

theorem commutator_of_first_zero (g h : Group n F) (hg : g.first = 0) :
    commutator g h = (⟨0,0,bracket h.first g.second⟩ : Group n F) := by
  ext <;> simp [commutator,hg,bracket] <;> ring_nf <;> simp

/-- The nested commutator has exactly the displayed cubic tensor. -/
theorem nested_commutator (g h : Group n F) :
    commutator (commutator g h) h =
      (⟨0,0,bracket h.first (quadraticBracket g.first h.first)⟩ : Group n F) := by
  rw [commutator_of_first_zero _ _ (commutator_first g h),commutator_second]

def tameWord (p : ℕ) (g h : Group n F) : Group n F := h*g*h⁻¹*(g^p)⁻¹

theorem tameWord_one (g h : Group n F) : tameWord 1 g h = h*g*h⁻¹*g⁻¹ := by
  simp [tameWord]

theorem tameWord_three (g h : Group n F) : tameWord 3 g h = tameWord 1 g h*g^2 := by
  have hg : g^3 = g⁻¹ := eq_inv_iff_mul_eq_one.mpr (by rw [← pow_succ]; exact pow_four g)
  simp only [tameWord,hg,inv_inv,pow_one,pow_two,mul_assoc,inv_mul_cancel_left]

@[simp] theorem tameWord_one_first (g h : Group n F) : (tameWord 1 g h).first = 0 := by
  simp [tameWord]

theorem tameWord_one_second (g h : Group n F) :
    (tameWord 1 g h).second = quadraticBracket g.first h.first := by
  rw [tameWord_one]
  funext i j
  simpa [quadraticBracket,add_comm] using Group.commutator_second h g i j

theorem tameWord_three_first (g h : Group n F) : (tameWord 3 g h).first = 0 := by
  rw [tameWord_three,mul_first,tameWord_one_first,square_first,add_zero]

theorem tameWord_three_second (g h : Group n F) :
    (tameWord 3 g h).second = quadraticBracket g.first h.first+squareTensor g.first := by
  rw [tameWord_three]
  ext i j
  simp [tameWord_one_second,square_second]

/-- Tame words with odd exponent have the square/bracket initial. -/
theorem tameWord_odd (p : ℕ) (hp : p % 4 = 1 ∨ p % 4 = 3) (g h : Group n F) :
    (tameWord p g h).first = 0 ∧
      (tameWord p g h).second = quadraticBracket g.first h.first +
        (if p % 4 = 3 then 1 else 0 : F) • squareTensor g.first := by
  have hm : tameWord p g h = tameWord (p % 4) g h := by
    unfold tameWord
    rw [pow_eq_pow_mod p (pow_four g)]
  rw [hm]
  rcases hp with hp | hp
  · rw [hp,tameWord_one_first,tameWord_one_second]
    simp
  · rw [hp,tameWord_three_first,tameWord_three_second]
    simp

namespace CutData
variable {m a b : ℕ} (C : CutData n m a b)
variable {G : Type} [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {x : Fin n → G}

/-- The full cubic Magnus map from the free universal property. -/
def freeDetector (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) :
    G →ₜ* Group n F :=
  hfree.liftHom hasPGroupOpenNormalBasis generator continuous_of_discreteTopology

@[simp] theorem freeDetector_generator
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (i : Fin n) :
    freeDetector hfree (x i) = generator i :=
  hfree.liftHom_apply hasPGroupOpenNormalBasis generator continuous_of_discreteTopology i

/-- The cut quotient, retaining the actual cubic tails of the relators. -/
def freeCut (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin m → V₃ n F) : G →ₜ* C.Cut tails where
  toMonoidHom := (C.quotientMap tails).comp (freeDetector hfree).toMonoidHom
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous (C.quotientMap tails)).comp
      (freeDetector hfree).continuous_toFun

@[simp] theorem freeCut_apply
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin m → V₃ n F) (g : G) :
    C.freeCut hfree tails g = C.quotientMap tails (freeDetector hfree g) := rfl

theorem freeCut_generator
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin m → V₃ n F) (i : Fin n) :
    C.freeCut hfree tails (x i) = C.quotientMap tails (generator i) := by simp

/-- Cubic coefficients are read from the relators. -/
def relatorTails (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (r : Fin m → G) : Fin m → V₃ n F := fun i => (freeDetector hfree (r i)).third

theorem freeCut_relator_eq_one
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (r : Fin m → G)
    (h1 : ∀ i, (freeDetector hfree (r i)).first = 0)
    (h2 : ∀ i, (freeDetector hfree (r i)).second = C.row i) (i : Fin m) :
    C.freeCut hfree (relatorTails hfree r) (r i) = 1 := by
  rw [freeCut_apply]
  have he : freeDetector hfree (r i) = (⟨0,C.row i,relatorTails hfree r i⟩ : Group n F) :=
    Group.ext (h1 i) (h2 i) rfl
  rw [he]
  exact (QuotientGroup.eq_one_iff _).mpr (C.relator_mem_cutSubgroup _ i)

theorem freeCut_central_eq_one
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin m → V₃ n F) (k : G) (z : V₃ n F)
    (hk : freeDetector hfree k = (⟨0,0,z⟩ : Group n F)) (hz : C.third z = 0) :
    C.freeCut hfree tails k = 1 := by
  rw [freeCut_apply,hk]
  exact (QuotientGroup.eq_one_iff _).mpr (C.central_mem_cutSubgroup tails z hz)

theorem freeDetector_eq_one_of_dimension_four
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (g : G)
    (hg : g ∈ GroupAugmentation.dimensionSubgroup F G 4) : freeDetector hfree g = 1 := by
  have h := GroupAugmentation.map_dimensionSubgroup_le F G
    (freeDetector hfree).toMonoidHom 4 ⟨g,hg,rfl⟩
  rw [dimensionSubgroup_four,Subgroup.mem_bot] at h
  exact h

/-- The finite image has a large conjugacy class of any element with vector `cVec`. -/
theorem freeCut_image_conjugacy_index_of_first
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin m → V₃ n F) (c : G) (hc : (freeDetector hfree c).first = C.cVec) :
    2^(a+b) ≤ (Subgroup.centralizer
      ({(⟨C.freeCut hfree tails c,⟨c,rfl⟩⟩ : (C.freeCut hfree tails).toMonoidHom.range)} :
        Set (C.freeCut hfree tails).toMonoidHom.range)).index := by
  let H := (C.freeCut hfree tails).toMonoidHom.range
  have hgen (i : Fin n) : C.quotientMap tails (generator i) ∈ H :=
    ⟨x i,C.freeCut_generator hfree tails i⟩
  exact C.conjugacy_index_lower_subgroup_of_first tails (freeDetector hfree c) hc H ⟨c,rfl⟩ hgen

/-- The Magnus first coordinate agrees with any continuous elementary map that
has the same values on the generators. -/
theorem freeDetector_first_eq
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (q : G →* Multiplicative (V₁ n F))
    (hq : @Continuous G (Multiplicative (V₁ n F)) _ ⊥ q)
    (hqx : ∀ i, q (x i) = Multiplicative.ofAdd (e i)) (g : G) :
    (freeDetector hfree g).first = (q g).toAdd := by
  let _ : TopologicalSpace (Multiplicative (V₁ n F)) := ⊥
  have _ : DiscreteTopology (Multiplicative (V₁ n F)) := ⟨rfl⟩
  have htwo : IsPGroup 2 (Multiplicative (V₁ n F)) := by
    apply IsPGroup.of_card (n := n)
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (V₁ n F) ≃ V₁ n F)]
    simp only [V₁,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  have hE : HasPGroupOpenNormalBasis 2 (Multiplicative (V₁ n F)) := by
    apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
    intro U
    exact ⟨inferInstance,htwo.of_surjective
      (QuotientGroup.mk' (U : Subgroup (Multiplicative (V₁ n F))))
      (QuotientGroup.mk'_surjective (U : Subgroup (Multiplicative (V₁ n F))))⟩
  let f : G →* Multiplicative (V₁ n F) :=
    Group.firstHom.comp (freeDetector hfree).toMonoidHom
  have hf : Continuous f :=
    (continuous_of_discreteTopology : Continuous (Group.firstHom (n := n) (R := F))).comp
      (freeDetector hfree).continuous_toFun
  have he : f = q := hfree.hom_ext hE hf hq (by
    intro i
    change Multiplicative.ofAdd (freeDetector hfree (x i)).first = q (x i)
    rw [freeDetector_generator,hqx]
    rfl)
  exact congrArg (Multiplicative.toAdd : Multiplicative (V₁ n F) → V₁ n F)
    (DFunLike.congr_fun he g)

end CutData
end UnitDistance.Sqrt241.Magnus
