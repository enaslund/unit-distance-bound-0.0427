module

public import UnitDistance.RationalLocalFiniteRestriction

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite restriction images have cardinalities independent of the
chosen embedding, for arbitrary (including nonabelian) source subgroups. -/
noncomputable section
namespace UnitDistance.GaloisEmbedding
variable {F M Ω G : Type*} [Field F] [Field M] [Field Ω] [Group G]
  [Algebra F M] [Algebra F Ω] [Module.Finite F M] [IsGalois F M]

theorem restriction_image_card_eq (f g : M →ₐ[F] Ω) (a : G →* Gal(Ω/F)) :
    Nat.card ((restriction f).toMonoidHom.comp a).range=
      Nat.card ((restriction g).toMonoidHom.comp a).range := by
  let u := (restriction f).toMonoidHom.comp a
  let v := (restriction g).toMonoidHom.comp a
  have hk : u.ker=v.ker := by
    ext σ
    exact restriction_eq_one_iff f g (a σ)
  calc
    Nat.card u.range=Nat.card (G ⧸ u.ker) :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange u).toEquiv).symm
    _ = Nat.card (G ⧸ v.ker) := by rw [hk]
    _ = Nat.card v.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange v).toEquiv

end UnitDistance.GaloisEmbedding
