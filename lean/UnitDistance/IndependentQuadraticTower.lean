module

public import UnitDistance.MultiquadraticTower

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual towers from independent squareclasses

The square kernel is recorded as a theorem about the actual algebra map.
Adjoining one square root enlarges that kernel by exactly its displayed
base squareclass.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.Multiquadratic
variable {ι E L : Type*} [DecidableEq ι] [Field E] [CharZero E]
  [Field L] [CharZero L] [Algebra E L]

/-- Base elements that become squares after adjoining the selected radicands. -/
def SquareKernel (a : ι → E) (s : Finset ι) : Prop :=
  ∀ b : E, IsSquare (algebraMap E L b) ↔
    ∃ t : Finset ι, t ⊆ s ∧ IsSquare (b / ∏ j ∈ t, a j)

theorem squareKernel_self (a : ι → E) : SquareKernel (L := E) a ∅ := by
  intro b
  simp [SquareKernel]

/-- The displayed square-kernel property is preserved by one actual
quadratic-algebra extension, with its exact new base squareclass. -/
theorem squareKernel_extension (a : ι → E) (s : Finset ι) (i : ι)
    [Fact (KummerInvariant.Nonsquare (algebraMap E L (a i)))]
    (hi : i ∉ s) (ha : a i ≠ 0) (hkernel : SquareKernel (L := L) a s) :
    SquareKernel (L := KummerInvariant.Extension (algebraMap E L (a i))) a (insert i s) := by
  intro b
  rw [IsScalarTower.algebraMap_apply E L (KummerInvariant.Extension (algebraMap E L (a i))),
    isSquare_algebraMap_iff _ _ (by simpa only [map_zero] using (algebraMap E L).injective.ne ha),
    ← map_div₀,hkernel b,hkernel (b/a i)]
  constructor
  · rintro (⟨t,ht,hb⟩ | ⟨t,ht,hb⟩)
    · exact ⟨t,ht.trans (Finset.subset_insert i s),hb⟩
    · refine ⟨insert i t,Finset.insert_subset_insert i ht,?_⟩
      have hit : i ∉ t := fun h => hi (ht h)
      simpa [Finset.prod_insert hit,div_mul_eq_div_div] using hb
  · rintro ⟨t,ht,hb⟩
    by_cases hit : i ∈ t
    · right
      refine ⟨t.erase i,?_,?_⟩
      · intro j hj
        have hjt := Finset.mem_of_mem_erase hj
        exact (Finset.mem_insert.mp (ht hjt)).resolve_left (Finset.ne_of_mem_erase hj)
      · rw [← Finset.insert_erase hit,Finset.prod_insert (by simp : i ∉ t.erase i)] at hb
        simpa [div_mul_eq_div_div] using hb
    · left
      refine ⟨t,?_,hb⟩
      intro j hj
      exact (Finset.mem_insert.mp (ht hj)).resolve_left (fun h => hit (h ▸ hj))

/-- Independent base squareclasses stay nonsquare until their own root is
adjoined; the premise refers only to genuine squares in the base field. -/
theorem nonsquare_next_of_squareKernel (a : ι → E) (s : Finset ι) (i : ι)
    (hi : i ∉ s) (ha : ∀ j, a j ≠ 0)
    (hind : ∀ t : Finset ι, t.Nonempty → ¬IsSquare (∏ j ∈ t, a j))
    (hkernel : SquareKernel (L := L) a s) :
    KummerInvariant.Nonsquare (algebraMap E L (a i)) := by
  apply nonsquare_of_not_isSquare
  intro hs
  obtain ⟨t,ht,hs⟩ := (hkernel (a i)).mp hs
  have hit : i ∉ t := fun h => hi (ht h)
  apply hind (insert i t) (Finset.insert_nonempty _ _)
  rw [Finset.prod_insert hit]
  have hp : (∏ j ∈ t, a j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => ha j
  have hmul := hs.mul (IsSquare.sq (∏ j ∈ t, a j))
  have he : a i / (∏ j ∈ t, a j) * (∏ j ∈ t, a j)^2 = a i * (∏ j ∈ t, a j) := by
    field_simp
  simpa only [he] using hmul

end UnitDistance.Multiquadratic

namespace UnitDistance.Multiquadratic
universe u
variable {ι : Type*} [DecidableEq ι] {E : Type u} [Field E] [CharZero E]

/-- A constructed actual multiquadratic extension, with its proved degree
and its exact square kernel on the base field. -/
structure ActualTower (a : ι → E) (s : Finset ι) where
  Carrier : Type u
  [field : Field Carrier]
  [charZero : CharZero Carrier]
  [algebra : Algebra E Carrier]
  [finite : Module.Finite E Carrier]
  [galois : IsGalois E Carrier]
  squareKernel : SquareKernel (L := Carrier) a s
  degree : Module.finrank E Carrier = 2^s.card

attribute [instance] ActualTower.field ActualTower.charZero ActualTower.algebra
  ActualTower.finite ActualTower.galois

/-- Every selected radicand has an actual square root in the constructed
field, as witnessed by the exact square kernel. -/
theorem ActualTower.isSquare_radical {a : ι → E} {s : Finset ι}
    (T : ActualTower a s) (i : ι) (hi : i ∈ s) (ha : a i ≠ 0) :
    IsSquare (algebraMap E T.Carrier (a i)) := by
  apply (T.squareKernel (a i)).mpr
  refine ⟨{i},Finset.singleton_subset_iff.mpr hi,?_⟩
  simpa [ha] using (IsSquare.one : IsSquare (1 : E))

/-- Independent squareclasses construct actual finite Galois extensions
of precisely the expected degree. -/
theorem exists_actualTower (a : ι → E) (ha : ∀ i, a i ≠ 0)
    (hind : ∀ t : Finset ι, t.Nonempty → ¬IsSquare (∏ j ∈ t, a j))
    (s : Finset ι) : Nonempty (ActualTower a s) := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨{
      Carrier := E
      galois := IsGalois.self E
      squareKernel := squareKernel_self a
      degree := by simp }⟩
  | @insert i s hi ih =>
    obtain ⟨T⟩ := ih
    let β : T.Carrier := algebraMap E T.Carrier (a i)
    letI : Fact (KummerInvariant.Nonsquare β) :=
      ⟨nonsquare_next_of_squareKernel a s i hi ha hind T.squareKernel⟩
    let L := KummerInvariant.Extension β
    letI : Module.Finite E L := Module.Finite.trans T.Carrier L
    letI : IsGalois E L := KummerInvariant.isGalois_of_invariant β (by
      intro σ
      exact ⟨1,by simp [β]⟩)
    exact ⟨{
      Carrier := L
      squareKernel := squareKernel_extension a s i hi (ha i) T.squareKernel
      degree := by
        rw [KummerInvariant.absolute_finrank, T.degree]
        simp only [Finset.card_insert_of_notMem hi,pow_succ]
        omega }⟩

end UnitDistance.Multiquadratic

namespace UnitDistance.Multiquadratic
universe u
variable {ι : Type*} [DecidableEq ι] {E : Type u} [Field E] [CharZero E]
  (k : Type*) [Field k] [Algebra k E]

/-- The constructed tower also remembers its actual algebra structure and
Galois property over the smaller ground field. -/
structure ActualGaloisTower (a : ι → E) (s : Finset ι) extends ActualTower a s where
  [baseAlgebra : Algebra k Carrier]
  [scalarTower : IsScalarTower k E Carrier]
  [baseGalois : IsGalois k Carrier]

attribute [instance] ActualGaloisTower.baseAlgebra ActualGaloisTower.scalarTower
  ActualGaloisTower.baseGalois

/-- Invariant independent base squareclasses construct an actual Galois
extension over the ground field, of the exact expected relative degree. -/
theorem exists_actualGaloisTower [Module.Finite k E] [IsGalois k E]
    (a : ι → E) (ha : ∀ i, a i ≠ 0)
    (hind : ∀ t : Finset ι, t.Nonempty → ¬IsSquare (∏ j ∈ t, a j))
    (hinvariant : ∀ i (σ : Gal(E/k)), ∃ u : E, a i*u^2 = σ (a i))
    (s : Finset ι) : Nonempty (ActualGaloisTower k a s) := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨{
      Carrier := E
      galois := IsGalois.self E
      squareKernel := squareKernel_self a
      degree := by simp }⟩
  | @insert i s hi ih =>
    obtain ⟨T⟩ := ih
    let β : T.Carrier := algebraMap E T.Carrier (a i)
    letI : Fact (KummerInvariant.Nonsquare β) :=
      ⟨nonsquare_next_of_squareKernel a s i hi ha hind T.squareKernel⟩
    let L := KummerInvariant.Extension β
    letI : Module.Finite k T.Carrier := Module.Finite.trans E T.Carrier
    letI : Module.Finite E L := Module.Finite.trans T.Carrier L
    letI : IsGalois E L := KummerInvariant.isGalois_of_invariant β (by
      intro σ
      exact ⟨1,by simp [β]⟩)
    letI : IsGalois k L := KummerInvariant.isGalois_of_invariant β (by
      intro σ
      obtain ⟨u,hu⟩ := hinvariant i (σ.restrictNormal E)
      refine ⟨algebraMap E T.Carrier u,?_⟩
      change algebraMap E T.Carrier (a i) * (algebraMap E T.Carrier u)^2 =
        σ (algebraMap E T.Carrier (a i))
      rw [← map_pow,← map_mul,hu,AlgEquiv.restrictNormal_commutes])
    exact ⟨{
      Carrier := L
      squareKernel := squareKernel_extension a s i hi (ha i) T.squareKernel
      degree := by
        rw [KummerInvariant.absolute_finrank, T.degree]
        simp only [Finset.card_insert_of_notMem hi,pow_succ]
        omega }⟩

end UnitDistance.Multiquadratic
