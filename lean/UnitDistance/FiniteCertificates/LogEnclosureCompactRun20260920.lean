module

public import UnitDistance.FiniteCertificates.Data

@[expose] public section
set_option backward.privateInPublic true


/-!
# Compact rational receipts for finite logarithm enclosures

The generated finite certificates state their finite arithmetic premises over
`ℚ`.  Kernel reduction proves those premises, and this lemma casts them once
into `ℝ` before applying the existing analytic logarithm enclosure.
-/

noncomputable section
set_option autoImplicit false

namespace UnitDistance.Witness.FiniteCertificates

theorem log_enclosure_of_rat (q : ℚ) (n : ℕ) (lo hi : ℚ)
    (hq : 1 ≤ q)
    (hl : lo ≤ 2 * ∑ i ∈ Finset.range n,
      ((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1))
    (hu : 2 * ((∑ i ∈ Finset.range n,
      ((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1)) +
      ((q - 1) / (q + 1)) ^ (2 * n + 1) /
        (1 - ((q - 1) / (q + 1)) ^ 2)) ≤ hi) :
    (lo : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (hi : ℝ) := by
  apply UnitDistance.log_enclosure (q : ℝ) n
  · exact_mod_cast hq
  · exact_mod_cast hl
  · exact_mod_cast hu

end UnitDistance.Witness.FiniteCertificates
