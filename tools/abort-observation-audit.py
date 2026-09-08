#!/usr/bin/env python3
"""Compiled post-import controls, selected from 7edc298f and adapted to main."""
from typed_audit import audit_main

mutations = [('AbortObservation',
  'GoLean.GoCore.AbortObservation',
  'abortObservationHole',
  '\nprivate axiom abortObservationHole : False\n'),
 ('RecoveryObservation',
  'GoLean.GoCore.RecoveryObservation',
  'abortObservationHole',
  '\nprivate axiom abortObservationHole : False\n'),
 ('RecoveryPoolObservation',
  'GoLean.GoCore.RecoveryPoolObservation',
  'abortObservationHole',
  '\nprivate axiom abortObservationHole : False\n'),
 ('RecoveryProgramObservation',
  'GoLean.GoCore.RecoveryProgramObservation',
  'abortObservationHole',
  '\nprivate axiom abortObservationHole : False\n'),
 ('audit_private',
  'Tests.AbortObservationAudit',
  'abortObservationAuditHole',
  '\nprivate axiom abortObservationAuditHole : False\n'),
 ('test_trailing',
  'Tests.AbortObservation',
  'sorryAx',
  '\nprivate theorem abortObservationTrailingHole : False := by sorry\n')]

if __name__ == "__main__":
    audit_main('abort-observation', 'import Tests.AbortObservationAudit\n#eval AbortObservationAudit.run\n', mutations)
