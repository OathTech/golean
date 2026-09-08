#!/usr/bin/env python3
"""Compiled post-import controls, selected from 7edc298f and adapted to main."""
from typed_audit import audit_main

mutations = [('core_private',
  'GoLean.GoCore.BooleanPreservation',
  'booleanRuntimeCoreHole',
  '\nprivate axiom booleanRuntimeCoreHole : False\n'),
 ('program_private',
  'GoLean.GoCore.BooleanProgram',
  'booleanRuntimeProgramHole',
  '\nprivate axiom booleanRuntimeProgramHole : False\n'),
 ('pool_private',
  'GoLean.GoCore.BooleanPool',
  'booleanRuntimePoolHole',
  '\nprivate axiom booleanRuntimePoolHole : False\n'),
 ('program_test_trailing',
  'Tests.BooleanProgram',
  'sorryAx',
  '\nprivate theorem booleanRuntimeProgramTestHole : False := by sorry\n'),
 ('audit_private',
  'Tests.BooleanSafetyAudit',
  'booleanRuntimeAuditHole',
  '\nprivate axiom booleanRuntimeAuditHole : False\n'),
 ('test_trailing',
  'Tests.BooleanInvariant',
  'sorryAx',
  '\nprivate theorem booleanRuntimeTrailingHole : False := by sorry\n')]

if __name__ == "__main__":
    audit_main('boolean-runtime', 'import Tests.BooleanSafetyAudit\n#eval BooleanSafetyAudit.run\n', mutations)
