#!/usr/bin/env python3
"""Compiled post-import controls, selected from 7edc298f and adapted to main."""
from typed_audit import audit_main

mutations = [('diagnostic_private',
  'GoLean.GoCore.RecoveryDiagnostics',
  'recoveryDiagnosticHole',
  '\nprivate axiom recoveryDiagnosticHole : False\n'),
 ('helper_private',
  'GoLean.GoCore.RecoveryCalls',
  'recoveryCallHole',
  '\nprivate axiom recoveryCallHole : False\n'),
 ('core_private',
  'GoLean.GoCore.RecoveryAdmission',
  'recoveryTypingCoreHole',
  '\nprivate axiom recoveryTypingCoreHole : False\n'),
 ('audit_private',
  'Tests.RecoveryTypingAudit',
  'recoveryTypingAuditHole',
  '\nprivate axiom recoveryTypingAuditHole : False\n'),
 ('test_trailing',
  'Tests.RecoveryTyping',
  'sorryAx',
  '\nprivate theorem recoveryTypingTrailingHole : False := by sorry\n')]

if __name__ == "__main__":
    audit_main('recovery-typing', 'import Tests.RecoveryTypingAudit\n#eval RecoveryTypingAudit.run\n', mutations)
