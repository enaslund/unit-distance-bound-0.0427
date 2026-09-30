module

public import SolutionZeta
public meta import AuditSupport

@[expose] public section
set_option backward.privateInPublic true


set_option maxHeartbeats 0
run_cmd UnitDistanceAudit.audit `UnitDistance
run_cmd UnitDistanceAudit.audit `UnitDistanceZetaSubmission

#print axioms UnitDistance.target_of_canonical_sharper_zeta_bound
#print axioms UnitDistanceZetaSubmission.target_of_canonical_zeta_bound
