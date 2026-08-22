# Spec interpretations — the curated index of adopted readings

Established 2026-08-19 (bug-fix arc, user-directed at the BUG-005
ruling). Where the pinned spec text (`deps/go`, go1.26.5) admits more
than one reading, the machine must still pick one — and that pick is a
DECISION with consequences, not a fact. This file is the one place
those decisions are indexed, so no session re-derives (or silently
re-decides) an interpretation.

Rules of the file:

- **One row per adopted reading.** Each row quotes the governing spec
  sentence(s), states OUR reading, names the REJECTED alternative, and
  lists what depends on the choice.
- **Every row is BACKED by a `docs/spec-divergence-ledger.md` entry**
  (the Cerberus-style sharp question, minimal program, and
  per-implementation data live THERE; this file is the index, not the
  argument). A reading without a ledger entry does not belong here —
  create the entry first.
- This file indexes READINGS of normative text. Latitude
  *realizations* (which member of an agreed envelope the machine pins)
  live in `docs/2026-08-11_latitude-inventory.md`; faults in the text
  itself live in the ledger under their own kinds.
- Changing a row is a doctrine-level act: it re-litigates everything in
  the row's "depends" column and needs the same class of sign-off that
  adopted it.

## The index

### I-1. A deleted-then-recreated map entry is a NEW entry — backed by L-012 (adopted 2026-08-19, user ruling)

- Spec (spec#For_statements, range clause, maps): "If a map entry that
  has not yet been reached is removed during iteration, the
  corresponding iteration value will not be produced." / "If a map
  entry is created during iteration, that entry may be produced during
  the iteration or may be skipped. The choice may vary for each entry
  created and from one iteration to the next." The text never defines
  entry identity across delete + re-create at the same key.
- OUR READING: the re-created entry is a NEW entry — created during
  iteration, so the may-produce-may-skip clause applies and it MAY BE
  PRODUCED AGAIN; deletion removes the key from the iteration's
  produced-set and from its mandatory (never-removed start keys) set.
- REJECTED: key-identity ("a key already produced is never produced
  again, even across delete + re-create") — no spec sentence keys
  "reached" by key, and it narrows the machine below the literal text
  (the BUG-005 memo's narrowing 1, rejected at the ruling).
- Depends on it (LANDED 2026-08-19, the (L) surgery): the surgery's
  produced-set semantics;
  corpus rows `maps/delete-readd-during-range` (admitted {3,4,-1}) and
  `maps/added-entry-count` ({1,2}); ∀-streams certification failing
  closed on self-inserting loops (genuinely unbounded traces under
  this reading); the kit obligation "body stores no key into the
  ranged map ⇒ range terminates".

### I-2. "not specified" evaluation order is UNSEQUENCED, not either-order — backed by L-013

- Spec (spec#Order_of_evaluation): "the order of those events compared
  to the evaluation and indexing of x and the evaluation of y ... is
  not specified."
- OUR READING: spec silence on order admits INTERLEAVINGS of the
  unordered events' observable sub-events (Cerberus's UNSEQ), not
  merely a per-expression choice between the two total orders.
- REJECTED: either-order (each expression evaluates under one of the
  two sequential orders) — strictly narrower; nothing in the text
  grants atomicity to the unordered event groups.
- Depends on it: the plausible-envelope statements of inventory
  E2–E5 and E12 (their F2 readings); every future re-envelope of the
  unordered-panic axes; membership-lane risk statements (too-narrow is
  the membership lane's job to catch).
- SCOPE NOTE (2026-08-22, launch audit D7 CRITICAL-2): for E12
  specifically, the row-level F2 sentence — whether E12's residue is
  an either-order or an interleaving claim — is still OWED in the
  inventory (E12's own words: "the F2 sentence owed alongside E2–E5";
  E13 concurs). This row adopts the UNSEQ reading as the GOVERNING
  DIRECTION; a session consuming E12 must not treat its per-row F2
  sentence as already written. Both readings are recorded and UNSEQ is
  the wider, doctrine-safe direction.

### I-3. A "may"-restriction's exhibit is one realization, not a mandate — backed by L-010

- Spec (spec#Return_statements): prose "Implementation restriction: A
  compiler may disallow an empty expression list in a 'return'
  statement if a different entity ... is in scope at the place of the
  return" vs. the same section's example labeled flatly
  "// invalid return statement: err is shadowed".
- OUR READING: the prose governs — a conforming implementation MAY
  accept the shadowed bare return; the exhibit records gc's
  realization.
- REJECTED: the exhibit governs (rejection is required).
- Depends on it: the negative-lane pin
  `negative/compile/spec-examples/bare-return-shadowed-result` is a
  gc-realization record, not a spec-forced one (its header says so);
  any future implementation-restriction row is read the same way.

### I-4. The init-order algorithm binds only observably-initializing packages — backed by L-011

- Spec (spec#Program_initialization): initialization proceeds over
  "a list of all packages, sorted by import path" (dependency-ready
  first).
- OUR READING: the algorithm constrains the observable order of
  packages that HAVE observable initialization work; a package with no
  residual init work may be omitted from the ready-race without
  violating the text (gc's pruning is conforming, and so is no
  pruning).
- REJECTED: the literal all-packages reading — refuted as the single
  binding order by gc disagreeing with ITSELF (the same source
  produces both orders under `-gcflags=all='-N -l'`; L-011's decisive
  row).
- Depends on it: `multipkg/init-order-*` pins (gc-at-default-flags
  realizations, re-envelope obligation open); BUG-061's residual.

### I-5. The spec is version-CONDITIONAL; our scope is the declared language version — backed by L-009

- Spec (spec#For_clause): "Prior to [Go 1.22], iterations share one
  set of variables" — one pinned document describing two behaviors
  gated on the module's go directive.
- OUR READING: the machine models the PINNED language version
  (go 1.26; ≥1.22 loopvar semantics); pre-gate behaviors are
  conforming FOR MODULES DECLARING older versions and are out of
  declared scope, recorded rather than modeled.
- REJECTED: "the spec text at the pin is unconditionally the
  language" (would demand modeling both sides of every version gate).
- Depends on it: mechanism 4.4's agreement rule (spec pin = oracle =
  corpus go directive); the loopvar corpus cases.

### I-6. The memory model's sequenced-before DELEGATES to the spec's evaluation order — backed by L-004

- Spec (mem#model, Requirement 1): "That execution must be consistent
  with the sequenced before relation, defined as the partial order
  requirements set out by the Go language specification for Go's
  control flow constructs as well as the order of evaluation for
  expressions."
- OUR READING: mem's sequenced-before is a PARTIAL order exactly where
  the spec's evaluation order is open — E-series latitude is
  memory-model latitude too, under concurrency.
- REJECTED: reading mem as imposing a total per-goroutine order
  (which would quietly close the E-series envelopes when a concurrent
  observer exists).
- Depends on it: any E-series envelope meeting a concurrent observer;
  the E1 cross-link recorded at the P2 retrofit.

### I-7. select's normative basis is spec-only — backed by L-005

- Spec: spec#Select_statements; the memory model contains NO select
  text (the absence is the record).
- OUR READING: C6/C7's envelopes are argued from the spec sentence
  alone ("uniform pseudo-random" enters possibilistically as "any");
  no implied memory-model guarantee is assumed.
- REJECTED: assuming an implicit mem guarantee for select commit
  order/visibility beyond the channel operations it performs.
- Depends on it: C6/C7's envelope statements; auditors stop hunting
  for a mem cite.
