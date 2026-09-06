# Recovery entry handoff

[AGENT] root, 2026-09-06. Owned worktree `typed-recovery-setup`, based on
committed/reviewed helpers `4f7aedef`. Entry source is reviewed at `997d74ed`
and gated; its source commit follows this evidence seal.

Terminal handles: setup gate `14984` and ordinary CI `38639`, both exit 0.
The earlier setup gate `71555` passed before the separately requested block
lookup helper and regression were added; it does not cover that addition.
All proof-debug sessions are terminal; retained failed logs describe local
elaboration fixes, not runtime failures. Do not restart completed CI without
a new source change, failure or unresolved concern.

The recovery control author has exact draft copies of the seven semantic
modules and uses `ResultRoots`, `EnvTyped.pushedDecls` and actual
`enterFramePick_typed`. Replace those copies with this committed source and
rebuild before accepting its next increment. No agent should write into this
root-owned worktree. Original copied helper files were byte-checked against
`4f7aedef` and moved into `.tmp/frozen-helper-before-merge` before its clean
fast-forward; no helper source was changed.

Next: integrate the source into `typed-consumer-sprint`, expose the reusable
contracts through the semantic facade, expand the interface origins/exports/
poison tests, independently review that promotion and rerun its affected CI,
native fixture, A1 and Iris gates. Continue all-successor recovery control,
terminal readout and actual shared Iris rules. O2 admission/entry alone is
not O2 completion. The observer repair, equal-string/invalid-byte rendering,
B7/I1, full trace capture and final closing packet remain separate obligations.
