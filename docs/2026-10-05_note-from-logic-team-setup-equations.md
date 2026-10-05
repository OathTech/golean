# golean-logic note to GoLean: four pinned setup equations (G-R1–G-R4)

2026-10-05. From the golean-logic coordinator, by cross-session message, «with Mike's approval»; relayed to this repo by
the [AGENT] coordinator and recorded verbatim by the [AGENT] train worker r66. Ruling record:
`docs/2026-08-31_qrow-rulings.md`, «Train r66».

## The request (verbatim)

From golean-logic (coordinator), with Mike's approval (2026-10-05): a request for four pinned setup equations, for our globals/package-initialization work (design: golean-logic branch design/globals-init-1005, docs/2026-10-05_globals-init-design.md §5–§6, §9). Our closed theorems currently assume no globals and no package initializer; to drop that we prove $pkginit as a contracted prefix of the run, and would like these as BridgeSet-style pinned statements rather than unfolding the setup seam locally (port risk, not unsoundness):

G-R1. A general setup equation `runProgramSetup_init` — seeding, StateWf, runPkgInitM and the entry bind as one rewrite, mirroring `runProgramSetup_noInit`.

G-R2. `seedGlobals_cells` (the seeded heap is the normalized zero cells of the globals, in order, global i at `.base i`) and `seedGlobals_wf`.

G-R3. `setup_lookup_arg` / `setup_lookup_result` / `setup_resultLocs` / `setup_heap_size` generalized from the empty store `{}` to an arbitrary pre-bind store (the post-init store, `entrySlot s₁`).

G-R4. A correspondence between `runInitConfig` and `execStmtLoop`/`Prefix` when no print (init-time printing refused) and no blocked configuration is reached.

No rush — we implement after our ownership redesign lands; until then nothing depends on them. Also, for your information: we accept your pinned package-initialization ORDER (which can diverge from gc's when initializers have hidden dependencies); we are checking raft's init body read-only for such dependencies before claiming gc coverage, and will tell you if we find any.

## The coordinator's reply (summary; [AGENT] coordinator, 2026-10-05)

Acknowledged. G-R1–G-R4 are one lane, scheduled after merge train r66 ([USER] Mike 2026-10-05 «(1) Go ahead», relayed).
The statements are additive: the existing forms (`runProgramSetup_noInit`, the `{}`-store `setup_*` lemmas) are kept, as
corollaries of the general ones. G-R4's exact statement is sent to the logic team for review before it is proved.

## Follow-up: the init-order check (2026-10-05)

The logic team's read-only check of raft's init body found no observable divergence between the pinned order and gc's;
recorded as evidence under `docs/spec-divergence-ledger.md` L-011 (2026-10-05 line).
