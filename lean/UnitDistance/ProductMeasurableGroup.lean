module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section
set_option backward.privateInPublic true


/-! # Product measurable additive groups

Coordinate proofs provide joint measurability for finite products, including
products with nonarchimedean factors which carry their explicit Borel measures.
-/

open MeasureTheory
namespace UnitDistance

instance measurableAdd₂Prod {G H : Type*} [Add G] [Add H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableAdd₂ G] [MeasurableAdd₂ H] :
    MeasurableAdd₂ (G × H) where
  measurable_add := (measurable_fst.fst.add measurable_snd.fst).prodMk
    (measurable_fst.snd.add measurable_snd.snd)

instance measurableNegProd {G H : Type*} [Neg G] [Neg H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableNeg G] [MeasurableNeg H] :
    MeasurableNeg (G × H) where
  measurable_neg := measurable_fst.neg.prodMk measurable_snd.neg

instance isNegInvariantProd {G H : Type*} [AddGroup G] [AddGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableNeg G] [MeasurableNeg H]
    (μ : Measure G) (ν : Measure H) [SFinite μ] [SFinite ν]
    [μ.IsNegInvariant] [ν.IsNegInvariant] : (μ.prod ν).IsNegInvariant where
  neg_eq_self := ((Measure.measurePreserving_neg μ).prod
    (Measure.measurePreserving_neg ν)).map_eq

end UnitDistance
