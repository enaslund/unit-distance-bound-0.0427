module

public import UnitDistance.SigmaPrimeSupport
public import Mathlib.Data.Finset.Card

@[expose] public section
set_option backward.privateInPublic true


/-! The actual six finite-place coordinates of the manuscript's ramification
support. Adapted from Yamaguchi/Sawin SixPrimeFiniteSupport, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0), with the actual support
2,3,5,7,11,13 instead of the source theorem's 3,5,7,11,13,17. -/
noncomputable section
open scoped NumberField
open IsDedekindDomain
namespace UnitDistance.ArithmeticProP

private def sigmaAllowedPrimes : Finset Nat.Primes :=
  {⟨2,by decide⟩,⟨3,by decide⟩,⟨5,by decide⟩,
    ⟨7,by decide⟩,⟨11,by decide⟩,⟨13,by decide⟩}

def sigmaFinitePrimeSupport : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  sigmaAllowedPrimes.map (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.toEmbedding

theorem mem_sigmaFinitePrimeSupport_iff (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ sigmaFinitePrimeSupport ↔ v ∈ sigmaPrimeSupport := by
  rw [sigmaFinitePrimeSupport,Finset.mem_map_equiv]
  change Rat.HeightOneSpectrum.primesEquiv v ∈ sigmaAllowedPrimes ↔
    (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∈ sigmaRationalPrimes
  let e : Nat.Primes ↪ ℕ := ⟨Subtype.val,Subtype.val_injective⟩
  have hm : sigmaAllowedPrimes.map e = sigmaRationalPrimes := by decide
  rw [← hm]
  exact (Finset.mem_map' e).symm

theorem sigmaFinitePrimeSupport_card : sigmaFinitePrimeSupport.card = 6 := by
  rw [sigmaFinitePrimeSupport,Finset.card_map]
  decide

end UnitDistance.ArithmeticProP
