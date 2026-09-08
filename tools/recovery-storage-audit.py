#!/usr/bin/env python3
"""Compiled post-import controls, selected from 7edc298f and adapted to main."""
from typed_audit import audit_main

mutations = [('RecoveryStore',
  'GoLean.GoCore.RecoveryStore',
  'recoveryStorageHole',
  '\nprivate axiom recoveryStorageHole : False\n'),
 ('RecoveryEnvironment',
  'GoLean.GoCore.RecoveryEnvironment',
  'recoveryStorageHole',
  '\nprivate axiom recoveryStorageHole : False\n'),
 ('RecoveryAllocation',
  'GoLean.GoCore.RecoveryAllocation',
  'recoveryStorageHole',
  '\nprivate axiom recoveryStorageHole : False\n'),
 ('RecoveryOperators',
  'GoLean.GoCore.RecoveryOperators',
  'recoveryStorageHole',
  '\nprivate axiom recoveryStorageHole : False\n'),
 ('RecoveryContext',
  'GoLean.GoCore.RecoveryContext',
  'recoveryStorageHole',
  '\nprivate axiom recoveryStorageHole : False\n'),
 ('RecoveryControlTyping',
  'GoLean.GoCore.RecoveryControlTyping',
  'recoveryStorageHole',
  '\nprivate axiom recoveryStorageHole : False\n'),
 ('audit_private',
  'Tests.RecoveryStorageAudit',
  'recoveryStorageAuditHole',
  '\nprivate axiom recoveryStorageAuditHole : False\n'),
 ('test_trailing',
  'Tests.RecoveryStorage',
  'sorryAx',
  '\nprivate theorem recoveryStorageTrailingHole : False := by sorry\n')]

if __name__ == "__main__":
    audit_main('recovery-storage', 'import Tests.RecoveryStorageAudit\n#eval RecoveryStorageAudit.run\n', mutations)
