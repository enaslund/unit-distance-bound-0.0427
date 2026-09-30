module

public import UnitDistance.Sqrt241.Local.TameAbsolute
public import UnitDistance.GroupAugmentationRetainedQuadratic

@[expose] public section
set_option backward.privateInPublic true

/-!
# The four tame places `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`: tables and finite-level labelled pairs

Tame places are indexed by `k : Fin 2` (the rational prime `3` or `5`) and
`P : Fin 2` (the prime of `B`: `0` for `iotaN`, `1` for `iotaN'`), or by
`q = tameIndex k P : Fin 4` (`𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`). The chosen place above `3`
(resp. `5`) lies over `tamePlace k`. Labels (construction.md §3.4):

| q | τ | φ |
|---|---|---|
| 𝔮₁ | `00001000` (16) | `10100111` (229) |
| 𝔮₂ | `00000100` (32) | `11101011` (215) |
| 𝔯₁ | `00000010` (64) | `01100101` (166) |
| 𝔯₂ | `00000001` (128) | `01011010` (90) |

`exists_absolute_tame_pair_at k` is the finite-level labelled tame pair at the
chosen place (`TameAbsolute.lean`) with the table of the prime of `B` below it.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField CanonicalGenus Base UnitDistance.PrimeCompletion Multiquadratic

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ## The chosen places above 3 and 5 -/

abbrev prime3 : Nat.Primes := ⟨3, Nat.prime_three⟩
abbrev prime5 : Nat.Primes := ⟨5, Nat.prime_five⟩

/-- The chosen place above `3`, restricted to `B`. -/
def emb3 : B →ₐ[ℚ] ℚ_[3] := placeEmb prime3 isSquare_241_three
/-- The chosen place above `5`, restricted to `B`. -/
def emb5 : B →ₐ[ℚ] ℚ_[5] := placeEmb prime5 isSquare_241_five

open Classical in
/-- `0` if the chosen place above `3` lies over `𝔮₁ = (π₃)`, else `1`. -/
def place3 : Fin 2 := if emb3 = iota3 then 0 else 1

open Classical in
/-- `0` if the chosen place above `5` lies over `𝔯₁ = (π₅)`, else `1`. -/
def place5 : Fin 2 := if emb5 = iota5 then 0 else 1

theorem emb3_eq (P : Fin 2) (h : place3 = P) : emb3 = ![iota3, iota3'] P := by
  rcases algHom_eq_iota3_or emb3 with he | he
  · have h0 : place3 = 0 := by simp [place3, he]
    rw [← h, h0, he]
    rfl
  · by_cases h' : emb3 = iota3
    · have h0 : place3 = 0 := by simp [place3, h']
      rw [← h, h0, h']
      rfl
    · have h1 : place3 = 1 := by simp [place3, h']
      rw [← h, h1, he]
      rfl

theorem emb5_eq (P : Fin 2) (h : place5 = P) : emb5 = ![iota5, iota5'] P := by
  rcases algHom_eq_iota5_or emb5 with he | he
  · have h0 : place5 = 0 := by simp [place5, he]
    rw [← h, h0, he]
    rfl
  · by_cases h' : emb5 = iota5
    · have h0 : place5 = 0 := by simp [place5, h']
      rw [← h, h0, h']
      rfl
    · have h1 : place5 = 1 := by simp [place5, h']
      rw [← h, h1, he]
      rfl

/-! ## Tables -/

/-- The rational prime of the tame place `k`: `3` or `5`. -/
abbrev tamePrime : Fin 2 → Nat.Primes := ![prime3, prime5]

/-- The prime of `B` under the chosen place above `tamePrime k`. -/
def tamePlace : Fin 2 → Fin 2 := ![place3, place5]

theorem tameIsSquare (k : Fin 2) : IsSquare (241 : ℚ_[(tamePrime k).val]) := by
  fin_cases k
  · exact isSquare_241_three
  · exact isSquare_241_five

/-- `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂` as `(k, P)`. -/
def tameIndex (k P : Fin 2) : Fin 4 := ![![0, 1], ![2, 3]] k P

/-- Square-class tables at the four tame places. -/
def tameClass : Fin 4 → Fin 8 → ℤ := ![squareclass3, squareclass3', squareclass5, squareclass5']
/-- Index of the ramified radicand (`π₃, π₃', π₅, π₅'`). -/
def tameRam : Fin 4 → Fin 8 := ![4, 5, 6, 7]
/-- Index of a nonresidue unit radicand (`-1` at 3, `ε` at 5). -/
def tameUnit : Fin 4 → Fin 8 := ![0, 0, 1, 1]
/-- The ramified class is `p · tameDw q` (`3 = 3·1`, `10 = 5·2`). -/
def tameDw : Fin 4 → ℤ := ![1, 1, 2, 2]
/-- The tame relation exponent `N = p`. -/
def tameN : Fin 4 → ℕ := ![3, 3, 5, 5]
def tameTauMask : Fin 4 → ℕ := ![16, 32, 64, 128]
def tamePhiMask : Fin 4 → ℕ := ![229, 215, 166, 90]
/-- Label of the inertia generator `τ` at the tame place `q`. -/
def tameTau (q : Fin 4) : Fin 8 → ZMod 2 := RetainedQuadratic.binaryVector 8 (tameTauMask q)
/-- Label of the normalized Frobenius `φ` at the tame place `q`. -/
def tamePhi (q : Fin 4) : Fin 8 → ZMod 2 := RetainedQuadratic.binaryVector 8 (tamePhiMask q)

theorem tameTau_eq : ∀ q : Fin 4, tameTau q = Pi.single (tameRam q) 1 := by decide +kernel

theorem tameN_eq : ∀ k P : Fin 2, tameN (tameIndex k P) = (tamePrime k).val := by decide +kernel

/-- Second-prime labels are `sigmaMatrix` of first-prime labels. -/
theorem sigmaMatrix_tameTau : ∀ k P : Fin 2,
    sigmaMatrix (tameTau (tameIndex k P)) = tameTau (tameIndex k (1 - P)) := by decide +kernel

theorem sigmaMatrix_tamePhi : ∀ k P : Fin 2,
    sigmaMatrix (tamePhi (tameIndex k P)) = tamePhi (tameIndex k (1 - P)) := by decide +kernel

/-- The data conditions of `exists_absolute_tame_pair` for all four tables. -/
theorem tame_table_conditions : ∀ k P : Fin 2,
    let q := tameIndex k P
    let p := (tamePrime k).val
    tameClass q (tameRam q) = (p : ℤ) * tameDw q ∧ ¬(p : ℤ) ∣ tameDw q ∧
    (∀ m, m ≠ tameRam q → ¬(p : ℤ) ∣ tameClass q m) ∧ tameUnit q ≠ tameRam q ∧
    ((tameClass q (tameUnit q) : ℤ) : ZMod p) ^ ((p - 1) / 2) = -1 ∧
    tamePhi q (tameRam q) = 0 ∧
    (∀ m, m ≠ tameRam q →
      ((tameClass q m : ℤ) : ZMod p) ^ ((p - 1) / 2) = binarySignInteger (tamePhi q m)) := by
  decide +kernel

theorem tame_placeEmb_alpha_three (m : Fin 8) : ∃ z : ℚ_[3], z ≠ 0 ∧
    emb3 (alphaB m) = (tameClass (tameIndex 0 place3) m : ℚ_[3]) * z ^ 2 := by
  rw [alphaB_eq]
  rcases Fin.exists_fin_two.mp ⟨place3, rfl⟩ with h | h
  · rw [emb3_eq 0 h, h]
    exact iota3_alpha m
  · rw [emb3_eq 1 h, h]
    exact iota3'_alpha m

theorem tame_placeEmb_alpha_five (m : Fin 8) : ∃ z : ℚ_[5], z ≠ 0 ∧
    emb5 (alphaB m) = (tameClass (tameIndex 1 place5) m : ℚ_[5]) * z ^ 2 := by
  rw [alphaB_eq]
  rcases Fin.exists_fin_two.mp ⟨place5, rfl⟩ with h | h
  · rw [emb5_eq 0 h, h]
    exact iota5_alpha m
  · rw [emb5_eq 1 h, h]
    exact iota5'_alpha m

/-- The square classes of the radicands at the chosen place above `tamePrime k`. -/
theorem tame_placeEmb_alpha (k : Fin 2) (m : Fin 8) :
    ∃ z : ℚ_[(tamePrime k).val], z ≠ 0 ∧
      placeEmb (tamePrime k) (tameIsSquare k) (alphaB m) =
        (tameClass (tameIndex k (tamePlace k)) m : ℚ_[(tamePrime k).val]) * z ^ 2 := by
  fin_cases k
  · exact tame_placeEmb_alpha_three m
  · exact tame_placeEmb_alpha_five m

/-- **Finite-level labelled tame pair at the chosen place above `3` or `5`.** -/
theorem exists_absolute_tame_pair_at (k : Fin 2)
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (j : M →ₐ[ℚ] Closure)
    (hM : IsPGroup 2 Gal(M/ℚ)) (hE : ∀ m, genusRoot m ∈ Set.range j) :
    ∃ t : AbsoluteInertia (tamePrime k), ∃ s : AbsoluteDecomposition (tamePrime k),
      HasLabel t.val.val (tameTau (tameIndex k (tamePlace k))) ∧
      HasLabel s.val (tamePhi (tameIndex k (tamePlace k))) ∧
      decompositionRestriction (tamePrime k) M j
        (s * t.val * s⁻¹ * (t.val ^ (tamePrime k).val)⁻¹) = 1 ∧
      (∀ x : AbsoluteInertia (tamePrime k), ∃ n : ℤ,
        decompositionRestriction (tamePrime k) M j x.val =
          (decompositionRestriction (tamePrime k) M j t.val) ^ n) ∧
      ∀ y : AbsoluteDecomposition (tamePrime k), decompositionRestriction (tamePrime k) M j y ∈
        Subgroup.closure ({decompositionRestriction (tamePrime k) M j t.val,
          decompositionRestriction (tamePrime k) M j s} : Set Gal(M/ℚ)) := by
  obtain ⟨hr, hdw, hunit, hur, hnr, hsvr, hsv⟩ := tame_table_conditions k (tamePlace k)
  have hp : (tamePrime k).val ≠ 2 := by fin_cases k <;> decide
  rw [tameTau_eq]
  exact exists_absolute_tame_pair (tamePrime k) (tameIsSquare k) hp _
    (tame_placeEmb_alpha k) _ _ _ hr hdw hunit hur hnr _ hsvr hsv M j hM hE

end UnitDistance.Sqrt241.Local
