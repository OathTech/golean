# TODO

Tactical backlog for the SEMANTICS product.

**Where the pre-split TODO went ([AGENT] ruling, recorded here per the
audit):** the pre-split TODO.md (907 lines) is preserved verbatim on
branch `park/reasoning-2026-08-31`. Its sections were triaged, not
just truncated: the sections with LIVE unchecked semantics items are
carried forward below (Enumerator optimization verbatim; W3.2 items by
headline with a park pointer); the reasoning-track items (iris-lean
refresh, campaign follow-up routing, proof generation) migrate with
that product; the remaining sections (work queue, epistemic hardening,
directional audit follow-ups, priority sequence, Goose/Perennial
matrix, differential execution, hardening phase, GoCore memory
milestone, 2026-08-09 follow-ups) are completed/superseded records —
consult them on the park branch, not here. If an item in those
sections turns out to be live, carry it forward with a note.

## Owed from the split (tracked in the split plan)

- GoCore relational-module extraction slice → the reasoning side
  ([USER]-ruled destination; [AGENT]-deferred past this slice because
  the modules are interleaved with the executable core). The full
  dependency cluster, enumerated at the audit: `Machine.lean`,
  `MachineSound.lean`, `Multi.lean` (the concurrent relation itself —
  imported by `EnumSpec.lean`, which the executable dedup engine
  needs), `MultiSound.lean`, `MultiWfSound.lean`, `MultiStreams.lean`,
  `NPDRF.lean`, `Race.lean`, plus the `StateEqb`/`SyntaxEqb`/
  `MachineEqb` seam. Needs a design slice + full `--diff`
  revalidation.
- `tools/raftsubject/twin-chdriver.go` + `twin-chdriver-main.go`:
  their Lean-side consumer (`TwinProgram.lean`) is parked; on main
  they remain exercised only by the twin-wire pin
  (`scripts/check-frontend-pins`). Revisit ownership at migration.
- `docs/architecture.md` and `docs/roadmap.md` semantics-scoped
  rewrites (currently carrying split banners).
- Migration stage ([USER] decisions): new repo name/location/
  dependency mechanism/history strategy; `raft-proof-campaign`
  branch disposition.

## Enumerator optimization layer (deferred backlog, 2026-08-07)

Record only — no implementation scheduled. Design of record:
`docs/2026-08-04_membership-lane-design.md`, section "Deferred: the
enumerator OPTIMIZATION layer (2026-08-07)" (provenance: user
discussion 2026-08-07). Layers, each behind the BOTH-EXPLORERS
adoption gate (optimized vs reference explorer, identical observation
sets on every tractable instance) and each with a named soundness
obligation:

- [ ] Verified POR — race-detector footprints as the independence
      oracle; NPDRF mover lemmas as its eventual proof.
- [ ] Symmetry reduction — decidable Config equality; the
      id-relabeling lemma is the soundness obligation.
- [ ] Preemption-bound-as-metadata — certificates must NAME their
      bound (bounded tree, never silently the full one).
- [ ] State memoization on canonicalized MultiConfig — requires the
      decidable-equality/canonicalization layer first.
- [ ] PCT / portfolio sampling beyond enumeration scale — sample
      source only, never certification.
- [ ] Map-range live-pick walk cost (BUG-005 (L), audit fix round
      2026-08-19 — a PERF item, not semantics): every `mapIterNext`
      pick recomputes `mapIterCandidates` = live entries minus the
      produced-key set (a linear scan filtered by a linear membership
      walk), so a full mutation-free range is ~O(n²) picks and the
      ∀-stream confluence certifier multiplies that again — ~cubic
      pick walks at scale. Invisible on today's corpus sizes; will
      bite on raft-scale maps and enumerator workloads. Candidate:
      an indexed produced-set (or incremental candidates) behind the
      BOTH-EXPLORERS adoption gate above, with the pick-coherence
      relation (`MapMem`) as the soundness obligation. Semantics is
      NOT in question — the fuel-out on self-inserting loops is the
      ruled behavior, not this item.

## Re-homed obligations (re-homed 2026-08-31, fidelity decision 6 [USER]; R15 by [AGENT] extension — see its entry)

The W3.2 and F4 arcs these obligations routed to are parked whole on
branch `park/reasoning-2026-08-31` — the routes dangled from the
split until this entry. Live owner for ALL of them: this backlog.
Each originating site (ledger §5.1/§6, BUGS.md) carries the matching
"(re-homed 2026-08-31, fidelity decision 6)" marker; the R15 sites
(inventory R15, ledger §2/§6) carry the [AGENT]-extension variant —
see the R15 entry below.

- [x] The eight Q-row rulings — the [USER] sitting HAPPENED 2026-08-31
      (fidelity decision 3); ruling record of record:
      `docs/2026-08-31_qrow-rulings.md` (supersedes the memos doc's
      §RULING SHEET by pointer). Six ruled: rows 6+7 (Q-SYNCVAL +
      Q-SYNCLIT) IMPLEMENTED 2026-09-01 on the qrow-syncval slice
      (7 reds flipped); rows 1/4/5/8 ruled with vehicles named
      (Q-INITSPAWN → standalone $pkginit backlog item; Q-RACEPATH →
      Tier-4 detector-soundness leg; Q-TRYLOCK/Q-COND → deferred with
      envelopes pre-ruled). Rows 2/3 OPEN with return conditions:
      Q-ATOMIC returns with an owner proposal (post Tier-4 scoping);
      Q-SELSEL after the C7 refresh + close-wake probe (queued S item).
- [ ] The `nonterm=`-under-`engine=dedup` ruling (charter OQ5,
      `docs/2026-08-20_w32-re-envelope-charter.md` §Open questions
      posed to the user;
      three candidate readings, and it changes what a green row
      asserts, so a [USER] ruling is owed) — live owner: this
      backlog. (Entry added at the 2026-08-31 audit fix round — the
      W3.2-section copy below is the historical text.)
- [ ] Q-ATOMICITY (= BUG-002, expression-step granularity — the
      formerly-F4 blocking precondition) and Q-GOEXIT (goroutine
      destruction): the two formerly-F4-owned design questions; held
      here until a concurrency-granularity arc exists.
- [ ] The (c)-pin re-envelope obligations (ledger §5.1 item 4): C1
      hidden-dep init order (E7 envelope), C2 staticinit `callinit`,
      C3 panic-qualifier rendering (BUG-059), C4 abort rendering
      (BUG-004), C5 float→int (R6) — formerly routed "to W3.2";
      C3/C6-class impossibility/out-of-language rows stay
      unconvertible, unchanged.
- [ ] BUG-004 + BUG-059: the display-vs-identity split and the
      abort-text member (semantic-core work formerly "owned by the
      W3.2 lane").
- [ ] BUG-065 residual (`goroutines/worker-pool/sum` honest red):
      formerly "awaiting the reduction/mover lane (slice 5)" — now a
      per-row ruling here, or a revived reduction lane.
- [ ] R15 zero-size-address re-envelope (may-equal choice or
      membership {0,1}; `pointers/zero-size-address/escaped-same`
      red) — formerly a "W3.2 re-envelope obligation". (re-homed
      2026-08-31 — [AGENT] extension of fidelity decision 6's orphan
      class; R15 fits the class; confirmed [USER] 2026-09-01)

## W3.2 re-envelope arc backlog (2026-08-20, charter DRAFT rev 1)

Semantics-side items carried by headline; full item text on the park
branch's TODO.md §"W3.2 re-envelope arc backlog". (The iris-lean
refresh and campaign-routing items from that section are
reasoning-side and migrate with that product. NOTE 2026-08-31: the
W3.2 arc itself is parked; the items below that are live semantics
obligations — the Q-row and `nonterm=` rulings — are duplicated with
owners in "Re-homed obligations" above, fidelity decision 6.)

- [ ] Trace-coverage push — PARKED POST-CAMPAIGN ([USER], 2026-08-21).
- [ ] Slice-5 probe: print-interleaving wedge-class candidate.
- [ ] RULE the eight Q-rows (charter §Slice 2 — memos written,
      rulings owed).
- [ ] RULE what `nonterm=` means under `engine=dedup`.
- [ ] Perf: map-iteration pick walks (post-BUG-005 (L) surgery; see
      the enumerator backlog's last item).

## Q-SELSEL implementation slot ([USER]-ruled 2026-09-01, option A)

- [ ] Q-SELSEL asymmetric-arrival envelope implementation (2 reds:
      the select-to-select rendezvous rows) — envelope adopted per
      docs/2026-08-31_qrow-rulings.md row 3; carry the owed C7
      wording correction at the sites; membership-lane case
      goroutines/select-wake-close-selsel recommended alongside
      (c7-refresh lane, 2026-09-01).

## Owed core fixes (BUGS.md carries the marker; this backlog the owner)

- [ ] BUG-078 residual (1): the LINEAR normalize. `normalizeListWith`
      (GoLean/GoCore/Ops.lean) is non-tail-recursive over the element
      list and quadratic (`#[head] ++ tail` per element); it sits
      arm-for-arm in lockstep with `isNormalForTyFuel` and the
      MachineSound soundness proofs (the de-WF recipe, 2026-08-03), so
      the rewrite is semantic-core surgery with a proof obligation on
      the parked reasoning side. Until it lands, `arrayLenBudget`
      (GoLean/NativeToIR.lean, 1<<16 — re-derived 2026-09-01 on the
      literal/store path, docstring states each number's path) refuses
      array TYPES past the bound by name; residual (3) — one element
      store into an admitted nested `[1024][1024][128]byte` measured
      46 s — is lifted by the same fix. Owner: this item ([AGENT]-
      recorded at the gotest-fixes audit fix round, RECORD 9). Exit:
      the budget constant retired or raised on a fresh re-measure, the
      over-budget red pin flipped or re-pinned at the new bound.

## Standing semantics backlog

- Coverage ledgers: consume-on-demand growth per
  `docs/coverage-suite-structure.md`; BUGS.md triage per
  `docs/bugfix-arc-log.md`.
- Spec-truth follow-ups (covmap CIPs held for sign-off:
  `docs/covmap-cips/`).
