/- Campaign Arc 2, probe B0: the compiled expected values for the
small-K kernel probes (the #eval-before-you-prove rule, CLAUDE.md).
Each kernel probe's `example : twinRun K [] = <expected>` uses exactly
the value this prints. Run:
  cd proofs && GOLEAN_MEM_MAX=16G ../scripts/capped \
    lake env lean ../docs/campaign-arc2-probes/probeB0-expected.lean
-/
import GoLeanProofs.Specs.RaftAgreement

open GoLean.Examples.RaftTwin

#eval do IO.println s!"K=0     : {repr (twinRun 0 [])}"
#eval do IO.println s!"K=10    : {repr (twinRun 10 [])}"
#eval do IO.println s!"K=100   : {repr (twinRun 100 [])}"
#eval do IO.println s!"K=1000  : {repr (twinRun 1000 [])}"
#eval do IO.println s!"K=10000 : {repr (twinRun 10000 [])}"
