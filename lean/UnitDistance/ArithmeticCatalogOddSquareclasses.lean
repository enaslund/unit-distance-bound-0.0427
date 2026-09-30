module

public import UnitDistance.ArithmeticCatalogIntegers
public import UnitDistance.RelativeUnramifiedOdd

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual local unit representatives for catalog squareclasses

At every odd prime of the actual genus field, one of each catalog element
and its conjugate is a unit. Their product is an actual square in the genus
field, so either representative has the same squareclass. Multiplication
gives an integral local unit representative for every raw catalog word.
-/
noncomputable section
namespace UnitDistance.ArithmeticCatalog
open ArithmeticChosenGenus NormExtensionCatalog NumberField
open scoped NumberField

/-- Exact integer Bézout coefficients for the catalog norm and trace. -/
def oddBezoutLeft : Fin 17 → ℤ :=
  ![2,-10,2,0,-2,0,2,22,-2,0,-1,2,2,2,-2,1,2]

def oddBezoutRight : Fin 17 → ℤ :=
  ![-16,76,-32,1,15,1,-1000,-158,14,1,17,-12,-104,-384,22,-3,6]

/-- The norm and trace of every catalog element generate an ideal containing two. -/
theorem catalog_odd_bezout (i : Fin 17) :
    oddBezoutLeft i*((catalog i).B*(catalog i).z^2) +
      oddBezoutRight i*(2*(catalog i).x) = 2 := by
  have h : ∀ i : Fin 17,
      oddBezoutLeft i*((catalog i).B*(catalog i).z^2) +
        oddBezoutRight i*(2*(catalog i).x) = 2 := by decide +kernel
  exact h i

theorem catalogInteger_sum (i : Fin 17) :
    catalogInteger i + catalogComplement i = (2*(catalog i).x : ℤ) := by
  apply Subtype.ext
  change alpha i (rootsA i)+alpha i (-(rootsA i)) =
    ((2*(catalog i).x : ℤ) : GenusField)
  push_cast
  unfold alpha
  ring

/-- The conjugate is in the actual squareclass of the original element. -/
theorem catalogComplement_squareclass (i : Fin 17) :
    ∃ c : GenusField, c ≠ 0 ∧
      (catalogComplement i : GenusField) = catalogAlpha i*c^2 := by
  let c : GenusField := (catalog i).z*rootsB i/catalogAlpha i
  have hz : ((catalog i).z : GenusField) ≠ 0 := by
    exact_mod_cast (catalog_nonzero i).2
  have hB : ((catalog i).B : GenusField) ≠ 0 := by
    exact_mod_cast (catalog_nonzero i).1
  have hb : rootsB i ≠ 0 := by
    intro h
    apply hB
    simpa [h] using (rootsB_sq i).symm
  have hα := catalogAlpha_ne_zero i
  refine ⟨c,div_ne_zero (mul_ne_zero hz hb) hα,?_⟩
  change alpha i (-(rootsA i)) =
    alpha i (rootsA i)*((catalog i).z*rootsB i/alpha i (rootsA i))^2
  symm
  calc
    alpha i (rootsA i)*((catalog i).z*rootsB i/alpha i (rootsA i))^2 =
        ((catalog i).B*((catalog i).z : GenusField)^2)/alpha i (rootsA i) := by
      rw [div_pow,mul_pow,rootsB_sq]
      field_simp
    _ = alpha i (-(rootsA i)) := (div_eq_iff hα).mpr (by
      simpa [mul_comm,catalogAlpha] using (alpha_norm i (rootsA i) (rootsA_sq i)).symm)

/-- At an odd prime, the catalog element and its conjugate cannot both vanish. -/
theorem catalogInteger_or_complement_not_mem (i : Fin 17)
    (P : Ideal (𝓞 GenusField)) (h2 : (2 : 𝓞 GenusField) ∉ P) :
    catalogInteger i ∉ P ∨ catalogComplement i ∉ P := by
  by_contra h
  push Not at h
  have hn : (((catalog i).B*(catalog i).z^2 : ℤ) : 𝓞 GenusField) ∈ P := by
    rw [← catalogInteger_product]
    exact P.mul_mem_right _ h.1
  have ht : ((2*(catalog i).x : ℤ) : 𝓞 GenusField) ∈ P := by
    rw [← catalogInteger_sum]
    exact P.add_mem h.1 h.2
  have heq : (oddBezoutLeft i : 𝓞 GenusField)*
      (((catalog i).B*(catalog i).z^2 : ℤ) : 𝓞 GenusField) +
      (oddBezoutRight i : 𝓞 GenusField)*((2*(catalog i).x : ℤ) : 𝓞 GenusField) = 2 := by
    exact_mod_cast catalog_odd_bezout i
  apply h2
  rw [← heq]
  exact P.add_mem (P.mul_mem_left _ hn) (P.mul_mem_left _ ht)

/-- Actual integral local-unit representative for every catalog squareclass. -/
theorem catalog_odd_unit_squareclass (i : Fin 17)
    (P : Ideal (𝓞 GenusField)) (h2 : (2 : 𝓞 GenusField) ∉ P) :
    ∃ (a : 𝓞 GenusField) (c : GenusField),
      c ≠ 0 ∧ (a : GenusField) = catalogAlpha i*c^2 ∧ a ∉ P := by
  rcases catalogInteger_or_complement_not_mem i P h2 with ha | ha
  · exact ⟨catalogInteger i,1,one_ne_zero,
      by
        change ((⟨catalogAlpha i, catalogAlpha_isIntegral i⟩ : 𝓞 GenusField) : GenusField) =
          catalogAlpha i * 1 ^ 2
        simpa using (NumberField.RingOfIntegers.coe_mk (catalogAlpha_isIntegral i)),ha⟩
  · obtain ⟨c,hc,heq⟩ := catalogComplement_squareclass i
    exact ⟨catalogComplement i,c,hc,heq,ha⟩

/-- Product closure for actual integral local-unit squareclass representatives. -/
theorem finite_product_unit_squareclass {ι : Type*} (s : Finset ι)
    (q : ι → GenusField) (P : Ideal (𝓞 GenusField)) [P.IsPrime]
    (hq : ∀ i ∈ s, ∃ (a : 𝓞 GenusField) (c : GenusField),
      c ≠ 0 ∧ (a : GenusField) = q i*c^2 ∧ a ∉ P) :
    ∃ (a : 𝓞 GenusField) (c : GenusField),
      c ≠ 0 ∧ (a : GenusField) = (∏ i ∈ s, q i)*c^2 ∧ a ∉ P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1,1,one_ne_zero,by simp,P.one_notMem⟩
  | @insert i s hi ih =>
    obtain ⟨a,c,hc,ha,haP⟩ := hq i (by simp)
    obtain ⟨b,d,hd,hb,hbP⟩ := ih (fun j hj => hq j (by simp [hj]))
    refine ⟨a*b,c*d,mul_ne_zero hc hd,?_,?_⟩
    · change (a : GenusField)*(b : GenusField) = _
      rw [Finset.prod_insert hi,ha,hb]
      ring
    · exact (inferInstance : P.IsPrime).mul_notMem haP hbP

/-- Every actual raw catalog word has an integral unit representative at every odd prime. -/
theorem word_odd_unit_squareclass (m : ℕ)
    (P : Ideal (𝓞 GenusField)) [P.IsPrime] (h2 : (2 : 𝓞 GenusField) ∉ P) :
    ∃ (a : 𝓞 GenusField) (c : GenusField),
      c ≠ 0 ∧ (a : GenusField) = wordRadicand m*c^2 ∧ a ∉ P := by
  exact finite_product_unit_squareclass
    (Finset.univ.filter fun i : Fin 17 => m.testBit i.val) catalogAlpha P
    (fun i _ => catalog_odd_unit_squareclass i P h2)

/-- Predicate form for actual relative ramification in any generated tower. -/
theorem word_hasOddLocalUnitSquareclass (m : ℕ) :
    QuadraticRamification.HasOddLocalUnitSquareclass GenusField (wordRadicand m) := by
  intro P hP h2
  exact word_odd_unit_squareclass m P h2

end UnitDistance.ArithmeticCatalog
