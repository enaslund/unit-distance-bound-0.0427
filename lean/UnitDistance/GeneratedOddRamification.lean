module

public import UnitDistance.GeneratedQuadraticEmbedding
public import UnitDistance.RelativeUnramifiedOdd

@[expose] public section
set_option backward.privateInPublic true


/-! Actual relative odd-prime unramifiedness for generated multiquadratic
fields whose radicands have integral local-unit squareclass representatives. -/
noncomputable section
open NumberField
namespace UnitDistance.Multiquadratic
open QuadraticRamification KummerInvariant
universe u
variable {ι : Type*} [DecidableEq ι] {E : Type u} [Field E] [NumberField E]

local instance generatedTower_numberField {a : ι → E} {s : Finset ι}
    (T : GeneratedGaloisTower ℚ a s) : NumberField T.Carrier :=
  NumberField.of_module_finite E T.Carrier

/-- A generated actual tower can be constructed together with its relative
odd-prime unramifiedness, from actual local-unit squareclass witnesses. -/
theorem exists_generatedGaloisTower_unramifiedAtOddPrimes [IsGalois ℚ E]
    (a : ι → E) (ha : ∀ i, a i ≠ 0)
    (hind : ∀ t : Finset ι, t.Nonempty → ¬IsSquare (∏ j ∈ t, a j))
    (hinvariant : ∀ i (σ : Gal(E/ℚ)), ∃ u : E, a i*u^2 = σ (a i))
    (hlocal : ∀ i, HasOddLocalUnitSquareclass E (a i))
    (s : Finset ι) :
    ∃ T : GeneratedGaloisTower ℚ a s, UnramifiedAtOddPrimes E T.Carrier := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨{
      Carrier := E
      galois := IsGalois.self E
      squareKernel := squareKernel_self a
      degree := by simp
      generated := by
        apply top_unique
        intro x _
        exact (Algebra.adjoin E (radicalSet (L := E) a ∅)).algebraMap_mem x }, unramifiedAtOddPrimes_refl E⟩
  | @insert i s hi ih =>
    obtain ⟨T,hT⟩ := ih
    let β : T.Carrier := algebraMap E T.Carrier (a i)
    letI : Fact (Nonsquare β) :=
      ⟨nonsquare_next_of_squareKernel a s i hi ha hind T.squareKernel⟩
    let L := Extension β
    letI : Module.Finite ℚ T.Carrier := Module.Finite.trans E T.Carrier
    letI : Module.Finite E L := Module.Finite.trans T.Carrier L
    letI : IsGalois E L := KummerInvariant.isGalois_of_invariant β (by
      intro σ
      exact ⟨1,by simp [β]⟩)
    letI : IsGalois ℚ T.Carrier := by
      have he : T.baseAlgebra = (DivisionRing.toRatAlgebra : Algebra ℚ T.Carrier) := Subsingleton.elim _ _
      rw [← he]
      exact T.baseGalois
    letI : IsGalois ℚ L := KummerInvariant.isGalois_of_invariant β (by
      intro σ
      obtain ⟨u,hu⟩ := hinvariant i (σ.restrictNormal E)
      refine ⟨algebraMap E T.Carrier u,?_⟩
      change algebraMap E T.Carrier (a i) * (algebraMap E T.Carrier u)^2 =
        σ (algebraMap E T.Carrier (a i))
      rw [← map_pow,← map_mul,hu,AlgEquiv.restrictNormal_commutes])
    have hL : UnramifiedAtOddPrimes E L := hT.trans
      (extension_unramifiedAtOddPrimes T.Carrier β
        (HasOddLocalUnitSquareclass.map E T.Carrier (hlocal i)))
    exact ⟨{
      Carrier := L
      squareKernel := squareKernel_extension a s i hi (ha i) T.squareKernel
      degree := by
        rw [KummerInvariant.absolute_finrank,T.degree]
        simp only [Finset.card_insert_of_notMem hi,pow_succ]
        omega
      generated := adjoin_radicalSet_extension a s i T.generated }, hL⟩

/-- The relative unramifiedness theorem applies to every actual choice-selected generated tower,
not only the auxiliary tower constructed while proving ramification. -/
theorem GeneratedGaloisTower.unramifiedAtOddPrimes [IsGalois ℚ E]
    {a : ι → E} {s : Finset ι} (T : GeneratedGaloisTower ℚ a s)
    (ha : ∀ i, a i ≠ 0)
    (hind : ∀ t : Finset ι, t.Nonempty → ¬IsSquare (∏ j ∈ t, a j))
    (hinvariant : ∀ i (σ : Gal(E/ℚ)), ∃ u : E, a i*u^2 = σ (a i))
    (hlocal : ∀ i, HasOddLocalUnitSquareclass E (a i)) :
    UnramifiedAtOddPrimes E T.Carrier := by
  obtain ⟨U,hU⟩ := exists_generatedGaloisTower_unramifiedAtOddPrimes a ha hind hinvariant hlocal s
  obtain ⟨f⟩ := U.nonempty_embedding T.Carrier (fun i hi => by
    obtain ⟨x,hx⟩ := T.toActualGaloisTower.toActualTower.isSquare_radical i hi (ha i)
    exact ⟨x,by simpa [pow_two] using hx.symm⟩)
  have hdim : Module.finrank E U.Carrier = Module.finrank E T.Carrier := U.degree.trans T.degree.symm
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f.toLinearMap)).mp f.injective
  exact hU.of_algEquiv (AlgEquiv.ofBijective f ⟨f.injective,hsurj⟩)

end UnitDistance.Multiquadratic
