module

public import UnitDistance.SigmaCutArithmeticWitness
public import UnitDistance.SigmaPresentation

@[expose] public section
set_option backward.privateInPublic true


/-! The actual arithmetic infinitude statement with its presentation
parameter discharged by the proved sharp six-relator presentation. -/
namespace UnitDistance.ArithmeticProP.SigmaCut

theorem arithmetic_presentation : ArithmeticPresentation :=
  sigmaOriginalRelator_generates

/-- The actual specified twenty-seven-word arithmetic cut is infinite. -/
theorem actualQuotient_infinite : Infinite ActualQuotient :=
  infinite_of_arithmeticPresentation arithmetic_presentation

end UnitDistance.ArithmeticProP.SigmaCut
