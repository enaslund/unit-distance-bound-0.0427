module

public import UnitDistance.PadicOddTamePair
public import UnitDistance.RationalGaloisBaseChange
public import UnitDistance.ArithmeticChosenGenusRoots
public import UnitDistance.UniversalQuadraticTame

@[expose] public section
set_option backward.privateInPublic true


/-! Actual odd local pairs in every finite rational Galois two-field containing the genus field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticOdd
open ArithmeticChosenGenus Multiquadratic

local instance oddPrime (i : Fin 5) : Fact (PadicOdd.primes i).Prime := ⟨PadicOdd.primes_prime i⟩

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  (g : GenusField →ₐ[ℚ] M) (i : Fin 5)

abbrev LocalField := RationalGaloisBaseChange.Carrier M ℚ_[PadicOdd.primes i]
abbrev localEmbedding := RationalGaloisBaseChange.embedding M ℚ_[PadicOdd.primes i]
abbrev restriction := RationalGaloisBaseChange.restriction M ℚ_[PadicOdd.primes i]
def localRoot (j : Fin 7) : LocalField M i := localEmbedding M i (g (roots j))

theorem localRoot_sq (j : Fin 7) :
    (localRoot M g i j)^2=(PadicOdd.radicands j : LocalField M i) := by
  rw [localRoot,← map_pow,← map_pow,roots_sq,map_ratCast,map_ratCast]
  have he : ∀ k : Fin 7, radicands k=(PadicOdd.radicands k : ℚ) := by decide +kernel
  rw [he]
  norm_cast

theorem restriction_genus_of_localSigns
    (σ : Gal(LocalField M i/ℚ_[PadicOdd.primes i])) (v : Fin 7 → ZMod 2)
    (hσ : ∀ j, σ (localRoot M g i j)=binarySign (v j)*localRoot M g i j) :
    GaloisEmbedding.restriction g (restriction M i σ)=signAutomorphism v := by
  apply automorphism_ext_roots
  intro j
  apply g.injective
  apply (localEmbedding M i).injective
  change localEmbedding M i (g (GaloisEmbedding.restriction g (restriction M i σ) (roots j)))=
    localEmbedding M i (g (signAutomorphism v (roots j)))
  rw [GaloisEmbedding.restriction_commutes]
  rw [RationalGaloisBaseChange.restriction_commutes]
  rw [signAutomorphism_roots,map_mul,map_mul]
  simpa only [binarySign,map_intCast,localRoot,localEmbedding] using hσ j

theorem inertia_vector (i : Fin 5) :
    UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)=
      Pi.single (PadicOdd.ramifiedIndex i) 1 := by
  have h : ∀ k : Fin 5, UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex k)=
      Pi.single (PadicOdd.ramifiedIndex k) 1 := by decide +kernel
  exact h i

theorem frobenius_sign_integer (i : Fin 5) (j : Fin 7) :
    binarySignInteger (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i) j)=
      PadicOdd.residueSign i j := by
  have h : ∀ k : Fin 5, ∀ l : Fin 7,
      binarySignInteger (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex k) l)=
        PadicOdd.residueSign k l := by decide +kernel
  exact h i j

/-- The finite arithmetic tame pair, obtained by actual local base change and restriction. -/
theorem exists_tame_pair (hM : IsPGroup 2 Gal(M/ℚ)) :
    ∃ τ φ : Gal(M/ℚ),
      GaloisEmbedding.restriction g τ=
        signAutomorphism (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) ∧
      GaloisEmbedding.restriction g φ=
        signAutomorphism (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) ∧
      φ*τ*φ⁻¹=τ^(UniversalQuadratic.oddPrimes i) := by
  obtain ⟨τ,φ,_hgen,hrel,hτ,hφ⟩ := PadicOddGenus.exists_labeled_tame_pair
    i (LocalField M i) (localRoot M g i) (localRoot_sq M g i)
    (RationalGaloisBaseChange.isPGroup M ℚ_[PadicOdd.primes i] hM)
  refine ⟨restriction M i τ,restriction M i φ,?_,?_,?_⟩
  · apply restriction_genus_of_localSigns
    intro j
    rw [inertia_vector]
    by_cases hj : j=PadicOdd.ramifiedIndex i
    · subst j
      simpa [binarySign,binarySignInteger] using hτ (PadicOdd.ramifiedIndex i)
    · simpa [binarySign,binarySignInteger,Pi.single_apply,hj,Ne.symm hj] using hτ j
  · apply restriction_genus_of_localSigns
    intro j
    simpa only [binarySign,frobenius_sign_integer] using hφ j
  · simpa only [map_mul,map_inv,map_pow] using congrArg (restriction M i) hrel

end UnitDistance.ArithmeticOdd
