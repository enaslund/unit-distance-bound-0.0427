module

public import SolutionZeta241
public meta import AuditSupport

@[expose] public section
set_option backward.privateInPublic true

set_option maxHeartbeats 0
run_cmd UnitDistanceAudit.audit `UnitDistance
run_cmd UnitDistanceAudit.audit `UnitDistanceSqrt241Submission

#print axioms UnitDistance.Sqrt241.V2.target_of_wide_zeta_bound
#print axioms UnitDistanceSqrt241Submission.target_of_wide_zeta_bound
