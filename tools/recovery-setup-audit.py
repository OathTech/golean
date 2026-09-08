#!/usr/bin/env python3
"""Compiled post-import controls, selected from 7edc298f and adapted to main."""
from typed_audit import audit_main

mutations = [('RecoverySetupShape',
  'GoLean.GoCore.RecoverySetupShape',
  'recoverySetupHole',
  '\nprivate axiom recoverySetupHole : False\n'),
 ('RecoveryInitialization',
  'GoLean.GoCore.RecoveryInitialization',
  'recoverySetupHole',
  '\nprivate axiom recoverySetupHole : False\n'),
 ('RecoveryResultRoots',
  'GoLean.GoCore.RecoveryResultRoots',
  'recoverySetupHole',
  '\nprivate axiom recoverySetupHole : False\n'),
 ('RecoverySetup',
  'GoLean.GoCore.RecoverySetup',
  'recoverySetupHole',
  '\nprivate axiom recoverySetupHole : False\n'),
 ('RecoverySetupWf',
  'GoLean.GoCore.RecoverySetupWf',
  'recoverySetupHole',
  '\nprivate axiom recoverySetupHole : False\n'),
 ('RecoverySetupReadout',
  'GoLean.GoCore.RecoverySetupReadout',
  'recoverySetupHole',
  '\nprivate axiom recoverySetupHole : False\n'),
 ('RecoveryCallEntry',
  'GoLean.GoCore.RecoveryCallEntry',
  'recoverySetupHole',
  '\nprivate axiom recoverySetupHole : False\n'),
 ('audit_private',
  'Tests.RecoverySetupAudit',
  'recoverySetupAuditHole',
  '\nprivate axiom recoverySetupAuditHole : False\n'),
 ('test_trailing',
  'Tests.RecoverySetup',
  'sorryAx',
  '\nprivate theorem recoverySetupTrailingHole : False := by sorry\n')]

if __name__ == "__main__":
    audit_main('recovery-setup', 'import Tests.RecoverySetupAudit\n#eval RecoverySetupAudit.run\n', mutations)
