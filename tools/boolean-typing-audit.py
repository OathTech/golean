#!/usr/bin/env python3
"""Compiled post-import controls, selected from 7edc298f and adapted to main."""
from typed_audit import audit_main

mutations = [('core_private',
  'GoLean.GoCore.BooleanTyping',
  'booleanTypingCoreHole',
  '\nprivate axiom booleanTypingCoreHole : False\n'),
 ('audit_private',
  'Tests.BooleanTypingAudit',
  'booleanTypingAuditHole',
  '\nprivate axiom booleanTypingAuditHole : False\n'),
 ('test_trailing',
  'Tests.BooleanTyping',
  'sorryAx',
  '\nprivate theorem booleanTypingTrailingHole : False := by sorry\n')]

if __name__ == "__main__":
    audit_main('boolean-typing', 'import Tests.BooleanTypingAudit\n#eval BooleanTypingAudit.run\n', mutations)
