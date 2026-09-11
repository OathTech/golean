# HANDOFF — lane `records/latitude-two-contracts-0911`

[AGENT] 2026-09-11. Records only; no runtime, baseline, or rule change;
no lake/lean run; no push, no merge. Worktree
`.claude/worktrees/latitude-two-contracts`, branched from main `a461ed8b`.

## What landed

- `89bac2a8` — `docs/2026-08-11_latitude-inventory.md` §11 (117 body
  lines): Contract A (portable Go 1.26 language semantics: modeled =
  permitted per site, the upper bound), Contract B (`Platform.gcAmd64`:
  the oracle pin's realization, the lower bound's object), the relation
  `observed ⊆ modeled ⊆ permitted` with which apparatus attacks which
  inclusion, and the 2026-09-11 review §6 gap list as seven classified
  items cross-referenced to existing sites (R1/R16, R4/R7, R2, R15,
  C1–C4/C6) or entered new (the finite `List Nat` tape). Plus a one-
  paragraph pointer at the end of the doctrine's «The two bounds».
  Authority: dispositions §4 step 2(ii), [USER] 2026-09-11 «Great, go
  ahead and land this, then launch the lanes» (relayed).
- This file (commit 2). NOTE [AGENT]: main's root `HANDOFF.md` at
  `a461ed8b` was the 2026-09-05 A2/BUG-103 integration handoff (last
  touched at `47195683`), the parking note of a programme SET ASIDE by
  the 2026-09-11 ruling; this lane's note replaces it at the root (the
  brief's required location). The prior text remains in history at
  `a461ed8b:HANDOFF.md`; preserving it as a dated doc is a one-line move
  at the train if the coordinator wants it — not done here.

Anchors: every `file:line` read at `a461ed8b`. Finding, not fixed: three
EXISTING inventory cites have drifted since the 2026-08-31 sweep (C1's
Multi.lean:220–224/:1153 → :400/:1511; §0 mirror's Machine.lean:963 →
:1387 and Ops.lean:1972 → :2383; R2's Ops.lean:1944–1972 → :2355–2384) —
recorded in §11's anchor note for the next cite sweep.

Checks run here (static; outputs under `.tmp/`, gitignored):
`tools/reconcile-records` exit 0, findings identical pre/post (C13 and C5
FR-7, both pre-existing); `scripts/check-evidence-size` exit 0;
`scripts/check-agents-alias` exit 0. NOT run: `scripts/check-spec-anchors`
(fails closed without `deps/go`, absent in this worktree) — the three
`spec#` tokens §11 uses were verified by grep against the primary
checkout's pinned `deps/go/doc/go_spec.html`; the train's `scripts/ci`
re-runs the lint properly.

## PENDING [USER] (posed in §11; nothing adjudicated here)

1. Item 1 — a 32-bit oracle host for a second `Platform` instance
   (machine-global; master plan §4 item 6).
2. Item 2 — R7's re-envelope shape: platform-faithful NaN rule vs an (a)
   envelope over the payloads gc's ports realize (BUG-094 PLAN).
3. Item 4 — whether/when to open the R15 zero-size may-equal lane (on the
   backlog since 2026-09-01).
4. Item 5 — `NPDRFReduction` restate-vs-delete (already PENDING per
   dispositions §3 item 2; restated, not re-posed).

## Audit ask

Posed. Proposal [AGENT]: waiver-eligible as a records-only change (two
docs, additive, counts unchanged, reconciler identical); the decision is
the user's.

## Exact next command (coordinator, from the primary checkout)

    git -C /home/dev/projects/golean diff main..records/latitude-two-contracts-0911 --stat
    git -C /home/dev/projects/golean diff main..records/latitude-two-contracts-0911 -- docs/

then, on explicit sign-off only:

    cd /home/dev/projects/golean && git checkout main && git merge --ff-only records/latitude-two-contracts-0911
