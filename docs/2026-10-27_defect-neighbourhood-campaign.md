# The defect-neighbourhood campaign — plan

STATUS: **APPROVED** ([USER] 2026-10-27: the four decisions of §6 ruled as
recommended — agreements on distinct routes pinned as rows; retired-construct
entries listed and marked, not swept; the sweep after train 21 and before the
release lane; the one-grep speedbump added. Plan written 2026-10-27 by the [AGENT]
coordinator on the owner's direction of 2026-10-26, paraphrased: go through the
history, log every semantic defect, then search locally around each — or make
sure a test case would catch it — as a pre-release activity.) Step 1 (the record
and its classification) starts at once, since it touches no code or corpus; step 2
waits for train 21.

## 1. Why

Every wrong answer found this month was an INSTANCE of a shape that had other
members: pointer identity through a struct conversion had five more routes
(BUG-133), the whole-struct value through the same conversion was refused on
eighteen (BUG-134), the pool's absorbing «not ready» default had a sibling in the
enumeration mirror (DC11 → F3), the `go.mod` directive refusals had `go.work`
beside them (BUG-135). The standing instruction is to investigate the local space
of each fix; it has been applied to the defects found since 2026-10-26 and not to
the 131 before them. The campaign applies it to the whole record, once, before the
release, so that the release's supported-scope statement rests on a corpus that
pins each known shape at its neighbours, not only at the instance that was found.

## 2. The record (step 1): what counts as a semantic defect, and where it is

- `docs/BUGS.md` is the single canonical index (its own header): a wrong value or a
  wrongly-stuck run on a construct the model claims to support. 133 entries on main
  `6e05137a` (136 after train 20): 117 fixed, 16 open, 11 red-by-design pins
  (`Expect: FAIL`); dated 1 / 62 / 33 / 2 across July–October (the Status lines).
  Two entries carry a neighbourhood table already (BUG-133, BUG-134).
- Outside the index, by policy nothing: a fidelity defect gets an entry. The
  campaign CHECKS that policy rather than assuming it: the commits whose messages
  mention a wrong answer (10 / 24 / 22 / 11 by month since July, `git log -i
  --grep`), the review documents (`docs/reviews/`, the Codex passes, the audits,
  `docs/2026-09-05_project-gate-audit.md`, the window logs) and the changelog rows
  are read for fixes that landed without an entry; each such fix gets a late
  entry (status fixed, Discovered: the commit) so the index is complete before
  step 2 begins.
- Scope limit: entries about constructs retired from the model (the parked
  typed-profile era, the retired relational layer) are listed and marked
  «retired construct», not swept.

Deliverable: `docs/defect-shapes.md` — one row per entry: id · status · the SITE
(file, function or arm) · the ROUTE it was found on · the SHAPE (§3) · whether a
neighbourhood was already swept · the sweep's lane once done. A living document
until the release; dated afterwards.

## 3. Shapes (the unit of step 2)

Classification is bottom-up: the lane that writes `defect-shapes.md` reads each
entry and names its shape in a few words, then normalizes the names into a
vocabulary of roughly fifteen to twenty-five shapes. Seed vocabulary from this
month's findings, to be revised by the reading, not imposed on it:

- representation leaks into identity (a static tag or index in `Loc` compared as
  address identity; `GoValue.eqb` where Go `==` was meant);
- a value crosses a conversion without the conversion's effect (retag, method set,
  dynamic type);
- an absorbing default (`| _ => false / none / the input`) reads a malformed or
  unexpected shape as benign;
- a run-time panic Go raises that the model does not (nil map write, index out of
  range, uncomparable dynamic type, negative shift, division), or raises with
  the wrong text or the wrong recoverability;
- evaluation order (unsequenced operands, defer/recover ordering, init order,
  select/channel fairness latitude taken as determinism);
- bounds and widths (overflow, truncation, signedness, float rounding and
  formatting, string/byte/rune indexing);
- zero values, nil-ness and aliasing (nil vs empty slice/map, zero-size
  allocations, per-iteration variables, closure capture);
- the frontend's lowering (declaration subsets, method sets and embedding,
  generics instantiation, stdlib overlays, module and workspace admission);
- the stdlib shims (a hand-written model diverging from the lowered source);
- concurrency (the scheduler's menu, parks and wakes, the race detector's keys,
  the main-exit window);
- the observation and readout (what is printed, how panics and exits are
  rendered, the membership lane's vocabulary).

## 4. The sweep (step 2): per shape, not per entry

For each shape, one lane, in the manner of BUG-133's neighbourhood table:

1. ENUMERATE the neighbourhood as a matrix — the same shape at the other types
   (every comparable kind; every container; named vs unnamed; generic
   instantiations), the other routes (`==`, map keys, interface boxes, switch,
   parameter binding, channel traffic, closures, the readout), the other sites
   (every arm of the same function; the drivers' mirrors; the proof-side
   copies). Write the matrix before probing.
2. PROBE every cell both sides (gc go1.26.5 under the runners' environment; the
   frontend and `golean native-json-run`); the race detector's cells over every
   schedule (`coverage-observations --expect-status`) against `go run -race`.
3. PIN: a disagreement is a finding → a BUG entry and a fix lane through the
   normal train (review, gate, ask); an agreement on a distinct route becomes a
   strict row (expected = gc) so the corpus holds the neighbour, not only the
   instance; a duplicate of an existing row is recorded as a probe id in the
   entry, not rowed; a refusal that is honest (named, `unsupported`) is recorded
   as a coverage gap; a refusal that misnames itself (`stuck` on a legal program)
   is a finding.
4. RECORD: a `- Neighbourhood:` line on every entry of the shape — the shape name,
   the matrix's extent (cells probed), the rows added, the cells left and why —
   and the shape's row in `defect-shapes.md` updated with the lane and the counts.

Order: shapes whose found instances were wrong answers with status ok come first
(identity, conversions, absorbing defaults, admission, panics), then wrongly-stuck
shapes, then the readout; within a shape the most recent instance first.

## 5. Checks, reviews, sizing

- One speedbump, one grep, report-only: every entry with `Status: fixed` dated
  on or after the campaign's start carries a `- Neighbourhood:` line
  (`scripts/check-bugs.sh` gains the test; a red names the entry). Not a gate:
  the trust surface is unchanged.
- Reviews, decorrelated as always: one on the classification (does
  `defect-shapes.md` miss defects the record holds; are the shapes well chosen —
  before the sweep starts), and the owner's second deep-clean pass (Codex, the
  owner's own prompt) after the sweep and the release lane, as the release
  claim-point review.
- Sizing from this month's measured lanes: the DC01 lane (one shape, 44 rows,
  six routes) took about 2.5 h wall including two full gates; the equality review
  (75 probes) 24 min; the struct-conversion lane (60 rows) about 1 h plus gates.
  Fifteen to twenty-five shapes, several already swept, at one lane each: about
  ten to twenty lane-runs, three or four at a time on the box, serialized by the
  build lock at a full gate of 15–20 min each — two to four days of box time.
  Each added hundred rows costs roughly 15 s of the differential run (4,157 rows
  take about 10 min of the 18-min gate); five hundred rows across the campaign
  is within the gate's budget.
- Trains: one per batch of shapes, with the standard review and ask; the
  campaign's findings follow the normal fix path, never a bulk re-pin.

## 6. Decisions for the owner

1. Scope of pinning: rows for every distinct-route agreement (recommended — cheap,
   permanent, and the corpus is the test suite by charter), or probes recorded in
   the entry only, with rows for disagreements and fixes.
2. The retired-construct entries: list-and-mark only (recommended), or sweep those
   whose shape still has live members.
3. Sequencing: after train 21 (the raft-proofs G21 lane) lands and before the
   release lane (recommended, as a pre-release activity); or interleaved with the
   release lane's records work, which does not touch the corpus.
4. The speedbump in §5: add it (recommended) or keep the practice manual.

## 7. Closure

The campaign closes with a dated report: entries covered / shapes / cells probed
/ rows added / defects found and fixed (each with its BUG id) / cells left open
by shape; `defect-shapes.md` dated; the release's supported-scope statement cites
it as the evidence that known shapes are pinned at their neighbours.
