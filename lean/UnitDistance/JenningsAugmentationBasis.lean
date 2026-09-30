module

public import UnitDistance.JenningsGenerators

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual augmentation monomial basis of every finite 2-group

The homogeneous generators come from the actual augmentation dimension
layers. Their ordered binary products cover the group. Replacing each
factor by its difference from one preserves spans by the proved triangular
span identities. The exact dimension-layer cardinality formula then proves
linear independence and gives an ordinary augmentation monomial basis.
This is not yet the assertion that its weights describe all actual powers.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G]

/-- The actual homogeneous generator differences in the convolution algebra. -/
def homogeneousDifferences : List (A (ZMod 2) G) :=
  (homogeneousGenerators G).map (fun g => delta (ZMod 2) g - 1)

/-- Binary ordered augmentation monomials in the actual homogeneous differences. -/
def augmentationMonomial := Jennings.binaryWord (homogeneousDifferences G)

omit [Finite G] in
/-- The group basis spans the actual convolution algebra. -/
theorem span_delta : Submodule.span (ZMod 2) (Set.range (delta (ZMod 2) (G := G))) = ⊤ := by
  have he : (fun g : G => delta (ZMod 2) g) = MonoidAlgebra.basis G (ZMod 2) := rfl
  change Submodule.span (ZMod 2) (Set.range (fun g : G => delta (ZMod 2) g)) = ⊤
  rw [he]
  exact (MonoidAlgebra.basis G (ZMod 2)).span_eq

/-- All actual ordered augmentation monomials span the group algebra. -/
theorem span_augmentationMonomial (hG : IsPGroup 2 G) :
    Submodule.span (ZMod 2) (Set.range (augmentationMonomial G)) = ⊤ := by
  rw [augmentationMonomial, Jennings.range_binaryWord]
  have hmap : homogeneousDifferences G =
      ((homogeneousGenerators G).map (MonoidAlgebra.of (ZMod 2) G)).map (fun x => x-1) := by
    simp [homogeneousDifferences, List.map_map, MonoidAlgebra.of_apply, delta, Function.comp_def]
  rw [hmap, Jennings.span_binaryWords_sub_one,
    Jennings.binaryWords_map, binaryWords_homogeneousGenerators G hG]
  rw [Set.image_univ]
  exact span_delta G

/-- The number of candidate monomials equals the actual group-algebra dimension. -/
theorem card_augmentationMonomials (hG : IsPGroup 2 G) :
    Fintype.card (Fin (homogeneousDifferences G).length → Bool) =
      Module.finrank (ZMod 2) (A (ZMod 2) G) := by
  letI : Fintype G := Fintype.ofFinite G
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    homogeneousDifferences, List.length_map, two_pow_length_homogeneousGenerators G hG,
    Module.finrank_eq_card_basis (MonoidAlgebra.basis G (ZMod 2)), Nat.card_eq_fintype_card]

/-- Independence follows from the proved spanning identity and exact
cardinality, rather than from an assumed PBW or filtered basis theorem. -/
theorem augmentationMonomials_independent (hG : IsPGroup 2 G) :
    LinearIndependent (ZMod 2) (augmentationMonomial G) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (le_of_eq (span_augmentationMonomial G hG).symm) (card_augmentationMonomials G hG)

/-- An ordinary basis of actual ordered augmentation monomials for every
finite 2-group, constructed from its actual homogeneous group directions. -/
def augmentationBasis (hG : IsPGroup 2 G) :
    Module.Basis (Fin (homogeneousDifferences G).length → Bool) (ZMod 2) (A (ZMod 2) G) :=
  basisOfTopLeSpanOfCardEqFinrank (augmentationMonomial G)
    (le_of_eq (span_augmentationMonomial G hG).symm) (card_augmentationMonomials G hG)

@[simp] theorem augmentationBasis_apply (hG : IsPGroup 2 G)
    (c : Fin (homogeneousDifferences G).length → Bool) :
    augmentationBasis G hG c = augmentationMonomial G c := by
  simp [augmentationBasis]

end UnitDistance.GroupAugmentation
