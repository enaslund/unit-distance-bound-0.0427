module

public import UnitDistance.Sqrt241.Levels.Export
public import UnitDistance.Sqrt241.DyadicLink.All

@[expose] public section
set_option backward.privateInPublic true


/-!
# The planar theorem at exponent `1.0427` from one genus-field inequality

The library endpoint of the ℚ(√241) development. The only hypothesis is the
numerical inequality H for the canonical genus field `E` (degree 512) of the
tower over `B = ℚ(√241)`; everything else is proved:

* the infinite 2-tower over `B`: the relation bound `Relation.OmegaB_h2` gives the
  presentation of `G_B` by seven relators (`Presentation.relators_generate`), which
  applies to the local elements `Local.localElements` (`Retained.input`); the
  Golod–Shafarevich inequality at `t = 34/117` then makes the cut quotient infinite
  (`Cut.SourceLifts.infinite_of_presentation`), also as a quotient of
  `Gal(Ω/ℚ)` (`Retained.Input.infinite_quotient`);
* its retained field `M` and the growing family of Galois fields with their local
  types, prime freedom and centralizer index (`Retained.towerData`);
* the root discriminant of `M` (`DyadicLink.log_rootDiscriminant_input_M`);
* the passage from H to the fixed-base ceiling of `M`
  (`fixedBaseCeiling_lt_of_genus_bound`), the numerical margin
  (`Witness.uniform_margin`) and the geometric construction
  (`target_of_growing_galois_fields`), combined in `target_of_tower_data`.

The proof below is `Retained.target_of_retained_tower`, which applies
`target_of_tower_data` to `Retained.towerData`, the root discriminant bound and H.
-/

noncomputable section
open NumberField
namespace UnitDistance.Sqrt241

/-- The planar sequence theorem at exponent `10427/10000`, from the displayed
inequality for the canonical genus field. -/
theorem target_of_canonical_genus_zeta_bound
    (hfinite : Real.log (dedekindZeta CanonicalGenus.Carrier
          ((1 + (1 / 300 : ℝ) : ℝ) : ℂ)).re / (512 : ℝ) + (1 / 300 : ℝ) *
        ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalGenus.Carrier) 2).re / (512 : ℝ)) <
        852 / 10000) :
    Target :=
  Retained.target_of_retained_tower DyadicLink.log_rootDiscriminant_input_M hfinite

end UnitDistance.Sqrt241
