import Tests.RecoveryTerminalAudit
open Lean
#eval show MetaM Unit from do
  let claims ← RecoveryTerminalAudit.claims
  liftM <| IO.println claims.compress
