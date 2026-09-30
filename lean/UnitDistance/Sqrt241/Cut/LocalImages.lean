module

public import UnitDistance.Sqrt241.Cut.LocalFamily

@[expose] public section
set_option backward.privateInPublic true


/-!
# The local groups embed in the cut quotient

With the labels, every local map into the cut quotient is injective (all
augmentation layers inject and the local groups are finite 2-groups): the
image of the dyadic local source at `𝔭_P` in the cut quotient is a copy of the
order-32 group `D`, the tame images are `C₂ × C₂`, the real images `C₂` and
the caps `C₄`. (For the local indices of admissible fields, `Levels/LocalData.lean`.)
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Cut
open GroupAugmentation GroupData

namespace SourceLifts
variable (A : SourceLifts) (r : LocalSource)
  (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
  (hgen : A.Presentation r) (hL : A.Labels)

include hL in
theorem dyadicQuotientMap_injective (P : Fin 2) :
    Function.Injective (A.dyadicQuotientMap r hr hgen P) :=
  dyadic_injective_of_layers (A.dyadicQuotientMap r hr hgen P).toMonoidHom
    (A.dyadicQuotientMap_layers r hr hgen hL P 1) (A.dyadicQuotientMap_layers r hr hgen hL P 2)

include hL in
/-- The image of the dyadic local group at `𝔭_P` has order 32. -/
theorem card_range_dyadicQuotientMap (P : Fin 2) :
    Nat.card (A.dyadicQuotientMap r hr hgen P).toMonoidHom.range = 32 := by
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (A.dyadicQuotientMap_injective r hr hgen hL P),
    Subgroup.card_top,Nat.card_eq_fintype_card,Dyadic.D.card]

/-- The image of the local source at `𝔭_P` in the cut quotient is the image of `D`. -/
theorem range_localSource (P : Fin 2) :
    (A.projection.comp (A.dyadic P)).toMonoidHom.range =
      (A.dyadicQuotientMap r hr hgen P).toMonoidHom.range := by
  ext q
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨Dyadic.ArithmeticPresentation.model g,A.dyadicQuotientMap_model r hr hgen P g⟩
  · rintro ⟨d,rfl⟩
    obtain ⟨g,rfl⟩ := Dyadic.ArithmeticPresentation.model_surjective d
    exact ⟨g,(A.dyadicQuotientMap_model r hr hgen P g).symm⟩

include hL in
theorem otherMap_injective (j : Index) : Function.Injective (A.otherMap r hr hgen j) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  injective_of_layer_injections (LocalGroup j) A.ActualQuotient (A.otherMap r hr hgen j) 2
    (localIsTwoGroup j) (A.otherMap_layers r hr hgen hL j)

end SourceLifts
end UnitDistance.Sqrt241.Cut
