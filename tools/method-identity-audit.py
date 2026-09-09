#!/usr/bin/env python3
"""[AGENT] Method identity: compiled unused poisons, post-import name checks."""
from typed_audit import audit_main

mutations = [
    ('member_private', 'GoLean.NativeDeclaration', 'methodIdentityMemberPoison',
     '\nprivate axiom methodIdentityMemberPoison : False\n'),
    ('decoder_private', 'GoLean.NativeToIR', 'methodIdentityDecoderPoison',
     '\nprivate axiom methodIdentityDecoderPoison : False\n'),
    ('test_hole', 'Tests.MethodIdentity', 'sorryAx',
     '\nprivate theorem methodIdentityTestPoison : False := by sorry\n'),
    ('audit_private', 'Tests.MethodIdentityAudit', 'methodIdentityAuditPoison',
     '\nprivate axiom methodIdentityAuditPoison : False\n'),
]

if __name__ == '__main__':
    audit_main('method-identity',
               'import Tests.MethodIdentityAudit\n#eval MethodIdentityAudit.run\n', mutations)
