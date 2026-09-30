# Candidate 17 post-seal mathematical-documentation errata

Candidate 17 is immutable, SHA-256
`3e369cb1cdc367fbb396946b9b69c1898a99d69cbb534b9b0d5ebe8cc29f1672`.
Its selected Lean proof inputs and exact H hypothesis are unchanged and
byte-identical to old-pinned verifier-passed archive 07. The points below
correct supporting paper prose, not the selected conditional theorem.

1. In the archived
   `verification/sol-luna-20260923/factor-inventory/h6-plus-all-prime-euler-and-analytic-data.md`,
   the sentence `Q=N_{B/Q}(𝔣(χ_{F/B}))` omits the base discriminant factor.
   Here `B=Q(√−35)` has `|disc(B)|=35`; the relative character conductor
   ideal has norm `N_{B/Q}(𝔣)=|disc(F)|/35²=6864` for the plus row, while
   the rational degree-two completed quotient conductor is
   `Q=35·N_{B/Q}(𝔣)=|disc(F)|/35=240240`. The numeric Q printed in candidate
   17 is correct. The checkout source note and all-32 corollary have been
   corrected, and the later paper all-32 conductor derivation uses the same
   normalization.
2. Some archived supporting notes call the degree-524288 retained field
   the “completed field.” The actual `ArithmeticCompleted.CompletedField`
   has degree 16384 and embeds in the degree-524288
   `CanonicalRetained.Carrier`/`ArithmeticRetained.RetainedField`. The new
   [placement audit](../sol-luna-20260923/factor-inventory/h6-all32-completed-field-placement.md)
   and checkout documentation distinguish them. This naming slip does not
   change the independently defined degree-524288 field in H.

Candidate 17 still passed its archived-source and finite package checks, but
those checks did not review or prove the supporting analytic prose. The
[corrected plus-row note](../sol-luna-20260923/factor-inventory/h6-plus-all-prime-euler-and-analytic-data.md)
and [assumption ledger](../../docs/ASSUMPTIONS.md) should be used when
assessing that argument. A future sealed candidate should incorporate these
corrections before any remote submission. H itself remains unproved in Lean.
