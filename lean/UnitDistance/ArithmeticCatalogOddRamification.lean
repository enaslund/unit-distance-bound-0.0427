module

public import UnitDistance.GeneratedOddRamification
public import UnitDistance.ArithmeticCatalogOddSquareclasses
public import UnitDistance.ArithmeticRetainedField
public import UnitDistance.ArithmeticCompletedField

@[expose] public section
set_option backward.privateInPublic true


/-! The actual finite fields M and N are unramified over the actual genus
field at every odd prime. The integral local-unit squareclass witnesses are
the concrete catalog identities; the generated fields are the existing
choice-selected carriers. -/
noncomputable section
namespace UnitDistance
open QuadraticRamification Multiquadratic

namespace ArithmeticRetained

/-- The actual degree2^19 retained field M is relatively unramified over its
seven-radical genus field at every prime not containing two. -/
theorem retainedField_unramifiedAtOddPrimes :
    UnramifiedAtOddPrimes ArithmeticChosenGenus.GenusField RetainedField := by
  apply fullRetainedTower.unramifiedAtOddPrimes retainedRadicand_ne_zero
    retained_products_not_isSquare retainedRadicand_invariant
  intro i
  exact ArithmeticCatalog.word_hasOddLocalUnitSquareclass
    (CatalogSquareclassData.retainedWords i)

end ArithmeticRetained

namespace ArithmeticCompleted

/-- The actual degree2^14 completed field N is relatively unramified over its
seven-radical genus field at every prime not containing two. -/
theorem completedField_unramifiedAtOddPrimes :
    UnramifiedAtOddPrimes ArithmeticChosenGenus.GenusField CompletedField := by
  apply completedTower.unramifiedAtOddPrimes completedRadicand_ne_zero
    completed_products_not_isSquare completedRadicand_invariant
  intro i
  exact ArithmeticCatalog.word_hasOddLocalUnitSquareclass
    (CatalogSquareclassData.completedWords i)

end ArithmeticCompleted
end UnitDistance
