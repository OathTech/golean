import VerdiCompat

/-!
# Differential-execution harness (design note §3, path 2 — Lean leg)

Seed-deterministic handler-level differential testing of the ported
Verdi Raft spec. This file is the LEAN side: it generates handler
inputs deterministically, runs the ported handlers, and records
`(input, output)` pairs in a committed fixture. `check` mode is a
REGRESSION PIN of the Lean port against its own recorded behavior —
it detects port drift.

THE ROCQ ORACLE LEG EXISTS (`compat/verdi/extraction/`, attached
2026-08-10 — lane log `docs/2026-08-09_verdi-p1-lane.md`, parking
ledger resolved): verdi-raft's own Coq handlers at the pinned rev,
instantiated with this same N=3 counter machine, extracted to OCaml
and replayed over the committed fixture's recorded inputs by
`extraction/build-and-run.sh`. Result on this fixture: 280/280
byte-identical outputs. What that validates: the Lean port's handler
semantics AGREE WITH THE COQ ORIGINALS on every recorded input, under
the counter instantiation — through the extraction TCB (Coq extraction
directives incl. nat→int and fin→int, plus OCaml evaluation). What it
does NOT validate: inputs outside the fixture, and the Prop-level
vocabulary (linearizability defs), which the oracle never executes.
The oracle run is manual/lane-local, not part of `check`; re-run it
whenever the fixture is regenerated.

## Fixture format (v1) — the contract the future Rocq leg codes against

- UTF-8 text; lines ending `\n`. Lines starting `#` are header.
- One case per line: `id<TAB>kind<TAB>input<TAB>output`.
- `kind` ∈ `hAE hAER hRV hRVR net inp reboot` (the four message
  handlers, the two composed handlers, crash-recovery).
- `input`/`output` are parenthesized s-expressions, space-separated,
  built from: `Nat` → decimal; `Fin N` (names) → decimal value;
  `Bool` → `true`/`false`; `Option` → `(none)` / `(some x)`;
  `List` → `(x1 x2 ...)`; pairs/tuples → `(a b ...)`;
  `entry` → `(entry eAt eClient eId eIndex eTerm eInput)`;
  `msg` → `(RequestVote t cand lli llt)` | `(RequestVoteReply t g)` |
  `(AppendEntries t lid pli plt (entries) lc)` |
  `(AppendEntriesReply t (entries) r)`;
  `raft_input` → `(Timeout)` | `(ClientRequest c id in)`;
  `raft_output` → `(NotLeader c id)` | `(ClientResponse c id out)`;
  `serverType` → `Follower`/`Candidate`/`Leader`;
  `raft_data` → `(state currentTerm votedFor leaderId (log) commitIndex
  lastApplied stateMachine (nextIndex) (matchIndex) shouldSend
  (votesReceived) type (clientCache) (electoralVictories))` with assoc
  lists as lists of pairs.
- Input shapes per kind (argument order = the ported handler's):
  `hAE`: `(me (state…) t lid pli plt (entries) lc)`;
  `hAER`: `(me (state…) src t (entries) result)`;
  `hRV`: `(me (state…) t cand lli llt)`;
  `hRVR`: `(me (state…) src t granted)`;
  `net`: `(me src (msg…) (state…))`; `inp`: `(me (input…) (state…))`;
  `reboot`: `((state…))`.
- Output shapes: `hAE`/`hRV`: `((state…) (msg…))`; `hAER`:
  `((state…) (packets))`; `hRVR`/`reboot`: `((state…))`;
  `net`/`inp`: `((outputs) (state…) (packets))`, packets as
  `(dst msg)` pairs.
- The machine is the Examples counter (data/input/output/clientId =
  Nat), N = 3. Per-case seed: `splitmix64` stream seeded
  `baseSeed + 1000003 * caseIndex` — cases are independent, so
  adding cases never perturbs existing ones. Inputs are recorded
  EXPLICITLY in the fixture: a replaying leg needs only a parser and
  the extracted handlers, never this generator.

## Modes (fail-closed)

- `generate <path>` — write the fixture.
- `check <path>` — regenerate and byte-compare against the committed
  fixture. Missing fixture = FAILURE (a run that checked nothing must
  not pass). Any difference = FAILURE with the first diverging line.
- anything else — refusal, exit 2.
-/

namespace VerdiCompat.DiffHarness

open VerdiCompat VerdiCompat.Raft VerdiCompat.Examples

abbrev CB := counterBase
abbrev Name3 := name (P := CB)
abbrev Entry3 := entry (P := CB)
abbrev Msg3 := msg (P := CB)
abbrev State3 := raft_data (P := CB)

/-! ## Deterministic PRNG (splitmix64) -/

/-- One splitmix64 step: `(value, nextState)`. Constants are the
reference ones (Steele–Lea–Flood); a replaying leg never needs them —
inputs are explicit in the fixture. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9E3779B97F4A7C15
  let z := s'
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s')

/-- Bounded draw: uniform-enough `Nat` below `n` (`n > 0`). -/
def rand (s : UInt64) (n : Nat) : Nat × UInt64 :=
  let (v, s) := splitmix s
  (v.toNat % n, s)

def randBool (s : UInt64) : Bool × UInt64 :=
  let (v, s) := rand s 2
  (v == 1, s)

def mkName (r : Nat) : Name3 :=
  ⟨r % 3, Nat.mod_lt _ (by decide)⟩

def randName (s : UInt64) : Name3 × UInt64 :=
  let (v, s) := rand s 3
  (mkName v, s)

def randOptName (s : UInt64) : Option Name3 × UInt64 :=
  let (b, s) := randBool s
  if b then
    let (n, s) := randName s
    (some n, s)
  else (none, s)

/-! ## Generators -/

def genEntry (s : UInt64) (idx tm : Nat) : Entry3 × UInt64 :=
  let (a, s) := randName s
  let (c, s) := rand s 3
  let (id, s) := rand s 4
  let (inp, s) := rand s 10
  (⟨a, c, id, idx, tm, inp⟩, s)

/-- A newest-first log with strictly decreasing indices and
non-increasing terms (the spec's `sorted` shape), length `len`. -/
def genSortedLog : (len : Nat) → UInt64 → (idx tm : Nat) → List Entry3 × UInt64
  | 0, s, _, _ => ([], s)
  | _ + 1, s, 0, _ => ([], s)  -- index floor reached: stop early
  | len + 1, s, idx + 1, tm =>
    let (e, s) := genEntry s (idx + 1) tm
    let (dTm, s) := rand s 2
    let (dIdx, s) := rand s 2
    let (rest, s) := genSortedLog len s (idx - dIdx) (tm - dTm)
    (e :: rest, s)

/-- Every 4th case gets a fully arbitrary (possibly unsorted) log:
the handlers are total functions and the differential covers them on
ill-formed states too. -/
def genRawLog : (len : Nat) → UInt64 → List Entry3 × UInt64
  | 0, s => ([], s)
  | len + 1, s =>
    let (idx, s) := rand s 10
    let (tm, s) := rand s 6
    let (e, s) := genEntry s idx tm
    let (rest, s) := genRawLog len s
    (e :: rest, s)

def genLog (caseIdx : Nat) (s : UInt64) : List Entry3 × UInt64 :=
  let (len, s) := rand s 5
  if caseIdx % 4 == 3 then genRawLog len s
  else
    let (idx, s) := rand s 9
    let (tm, s) := rand s 6
    genSortedLog len s idx tm

def genAssoc : (len : Nat) → UInt64 → List (Name3 × Nat) × UInt64
  | 0, s => ([], s)
  | len + 1, s =>
    let (n, s) := randName s
    let (v, s) := rand s 9
    let (rest, s) := genAssoc len s
    ((n, v) :: rest, s)

def genNames : (len : Nat) → UInt64 → List Name3 × UInt64
  | 0, s => ([], s)
  | len + 1, s =>
    let (n, s) := randName s
    let (rest, s) := genNames len s
    (n :: rest, s)

def genCache : (len : Nat) → UInt64 → List (Nat × (Nat × Nat)) × UInt64
  | 0, s => ([], s)
  | len + 1, s =>
    let (c, s) := rand s 3
    let (id, s) := rand s 5
    let (o, s) := rand s 20
    let (rest, s) := genCache len s
    ((c, (id, o)) :: rest, s)

def genServerType (s : UInt64) : serverType × UInt64 :=
  let (v, s) := rand s 3
  (if v == 0 then .Follower else if v == 1 then .Candidate else .Leader, s)

def genState (caseIdx : Nat) (s : UInt64) : State3 × UInt64 :=
  let (ct, s) := rand s 6
  let (vf, s) := randOptName s
  let (lid, s) := randOptName s
  let (log, s) := genLog caseIdx s
  let (ci, s) := rand s 9
  let (la, s) := rand s 9
  let (sm, s) := rand s 30
  let (niLen, s) := rand s 4
  let (ni, s) := genAssoc niLen s
  let (miLen, s) := rand s 4
  let (mi, s) := genAssoc miLen s
  let (ss, s) := randBool s
  let (vrLen, s) := rand s 4
  let (vr, s) := genNames vrLen s
  let (ty, s) := genServerType s
  let (ccLen, s) := rand s 3
  let (cc, s) := genCache ccLen s
  ({ currentTerm := ct, votedFor := vf, leaderId := lid, log := log
     commitIndex := ci, lastApplied := la, stateMachine := sm
     nextIndex := ni, matchIndex := mi, shouldSend := ss
     votesReceived := vr, type := ty, clientCache := cc
     electoralVictories := [] }, s)

def genMsg (caseIdx : Nat) (s : UInt64) : Msg3 × UInt64 :=
  let (v, s) := rand s 4
  match v with
  | 0 =>
    let (t, s) := rand s 6
    let (c, s) := randName s
    let (lli, s) := rand s 9
    let (llt, s) := rand s 6
    (.RequestVote t c lli llt, s)
  | 1 =>
    let (t, s) := rand s 6
    let (g, s) := randBool s
    (.RequestVoteReply t g, s)
  | 2 =>
    let (t, s) := rand s 6
    let (lid, s) := randName s
    let (pli, s) := rand s 9
    let (plt, s) := rand s 6
    let (log, s) := genLog caseIdx s
    let (lc, s) := rand s 9
    (.AppendEntries t lid pli plt log lc, s)
  | _ =>
    let (t, s) := rand s 6
    let (log, s) := genLog caseIdx s
    let (r, s) := randBool s
    (.AppendEntriesReply t log r, s)

def genInput (s : UInt64) : raft_input (P := CB) × UInt64 :=
  let (v, s) := rand s 2
  if v == 0 then (.Timeout, s)
  else
    let (c, s) := rand s 3
    let (id, s) := rand s 5
    let (inp, s) := rand s 10
    (.ClientRequest c id inp, s)

/-! ## Canonical serialization (format v1; see module docstring) -/

def serList {A : Type} (f : A → String) (l : List A) : String :=
  "(" ++ " ".intercalate (l.map f) ++ ")"

def serOpt {A : Type} (f : A → String) : Option A → String
  | none => "(none)"
  | some x => "(some " ++ f x ++ ")"

def serNat (n : Nat) : String := toString n

def serName (n : Name3) : String := toString n.val

def serEntry (e : Entry3) : String :=
  s!"(entry {serName e.eAt} {serNat e.eClient} {e.eId} {e.eIndex} {e.eTerm} {serNat e.eInput})"

def serMsg : Msg3 → String
  | .RequestVote t c lli llt => s!"(RequestVote {t} {serName c} {lli} {llt})"
  | .RequestVoteReply t g => s!"(RequestVoteReply {t} {g})"
  | .AppendEntries t lid pli plt es lc =>
    s!"(AppendEntries {t} {serName lid} {pli} {plt} {serList serEntry es} {lc})"
  | .AppendEntriesReply t es r =>
    s!"(AppendEntriesReply {t} {serList serEntry es} {r})"

def serInput : raft_input (P := CB) → String
  | .Timeout => "(Timeout)"
  | .ClientRequest c id inp => s!"(ClientRequest {serNat c} {id} {serNat inp})"

def serOutput : raft_output (P := CB) → String
  | .NotLeader c id => s!"(NotLeader {serNat c} {id})"
  | .ClientResponse c id o => s!"(ClientResponse {serNat c} {id} {serNat o})"

def serServerType : serverType → String
  | .Follower => "Follower"
  | .Candidate => "Candidate"
  | .Leader => "Leader"

def serNatPair (p : Name3 × Nat) : String := s!"({serName p.1} {p.2})"

def serCacheEntry (p : Nat × (Nat × Nat)) : String :=
  s!"({p.1} {p.2.1} {p.2.2})"

def serVictory (v : Nat × List Name3 × List Entry3) : String :=
  s!"({v.1} {serList serName v.2.1} {serList serEntry v.2.2})"

def serState (st : State3) : String :=
  s!"(state {st.currentTerm} {serOpt serName st.votedFor} " ++
  s!"{serOpt serName st.leaderId} {serList serEntry st.log} " ++
  s!"{st.commitIndex} {st.lastApplied} {serNat st.stateMachine} " ++
  s!"{serList serNatPair st.nextIndex} {serList serNatPair st.matchIndex} " ++
  s!"{st.shouldSend} {serList serName st.votesReceived} " ++
  s!"{serServerType st.type} {serList serCacheEntry st.clientCache} " ++
  s!"{serList serVictory st.electoralVictories})"

def serPacket (p : Name3 × Msg3) : String :=
  s!"({serName p.1} {serMsg p.2})"

def serHandlerResult
    (r : List (raft_output (P := CB)) × State3 × List (Name3 × Msg3)) : String :=
  s!"({serList serOutput r.1} {serState r.2.1} {serList serPacket r.2.2})"

/-! ## Cases -/

def kinds : List String := ["hAE", "hAER", "hRV", "hRVR", "net", "inp", "reboot"]

/-- Run one case: `(input-sexp, output-sexp)`. Every draw is recorded in
the input serialization; the output is the ported handler's answer. -/
def runCase (kind : String) (caseIdx : Nat) (s : UInt64) :
    Option (String × String) :=
  match kind with
  | "hAE" =>
    let (me, s) := randName s
    let (st, s) := genState caseIdx s
    let (t, s) := rand s 6
    let (lid, s) := randName s
    let (pli, s) := rand s 9
    let (plt, s) := rand s 6
    let (es, s) := genLog caseIdx s
    let (lc, _) := rand s 9
    let r := handleAppendEntries me st t lid pli plt es lc
    some (s!"({serName me} {serState st} {t} {serName lid} {pli} {plt} {serList serEntry es} {lc})",
          s!"({serState r.1} {serMsg r.2})")
  | "hAER" =>
    let (me, s) := randName s
    let (st, s) := genState caseIdx s
    let (src, s) := randName s
    let (t, s) := rand s 6
    let (es, s) := genLog caseIdx s
    let (res, _) := randBool s
    let r := handleAppendEntriesReply me st src t es res
    some (s!"({serName me} {serState st} {serName src} {t} {serList serEntry es} {res})",
          s!"({serState r.1} {serList serPacket r.2})")
  | "hRV" =>
    let (me, s) := randName s
    let (st, s) := genState caseIdx s
    let (t, s) := rand s 6
    let (cand, s) := randName s
    let (lli, s) := rand s 9
    let (llt, _) := rand s 6
    let r := handleRequestVote me st t cand lli llt
    some (s!"({serName me} {serState st} {t} {serName cand} {lli} {llt})",
          s!"({serState r.1} {serMsg r.2})")
  | "hRVR" =>
    let (me, s) := randName s
    let (st, s) := genState caseIdx s
    let (src, s) := randName s
    let (t, s) := rand s 6
    let (g, _) := randBool s
    let r := handleRequestVoteReply me st src t g
    some (s!"({serName me} {serState st} {serName src} {t} {g})",
          s!"({serState r})")
  | "net" =>
    let (me, s) := randName s
    let (src, s) := randName s
    let (m, s) := genMsg caseIdx s
    let (st, _) := genState caseIdx s
    let r := RaftNetHandler me src m st
    some (s!"({serName me} {serName src} {serMsg m} {serState st})",
          serHandlerResult r)
  | "inp" =>
    let (me, s) := randName s
    let (i, s) := genInput s
    let (st, _) := genState caseIdx s
    let r := RaftInputHandler me i st
    some (s!"({serName me} {serInput i} {serState st})",
          serHandlerResult r)
  | "reboot" =>
    let (st, _) := genState caseIdx s
    let r := reboot (P := CB) st
    some (s!"({serState st})", s!"({serState r})")
  | _ => none  -- unknown kind: refused upstream, never silently skipped

def baseSeed : UInt64 := 42
def casesPerKind : Nat := 40

/-- All case lines, or the first unknown kind (fail closed). -/
def caseLines : Except String (List String) := do
  let numbered := kinds.flatMap fun k =>
    (List.range casesPerKind).map fun i => (k, i)
  let rec build (cases : List (String × Nat)) (caseIdx : Nat) :
      Except String (List String) := do
    match cases with
    | [] => pure []
    | (kind, _) :: rest =>
      let seed := baseSeed + 1000003 * UInt64.ofNat caseIdx
      match runCase kind caseIdx seed with
      | none => throw s!"unknown case kind '{kind}' — refusing to emit a fixture"
      | some (inp, out) =>
        let line := s!"{caseIdx}\t{kind}\t{inp}\t{out}"
        let rest ← build rest (caseIdx + 1)
        pure (line :: rest)
  build numbered 0

def header : List String :=
  [ "# verdi-diff-fixture v1"
  , s!"# machine=counter N=3 base-seed={baseSeed} cases-per-kind={casesPerKind} kinds={" ".intercalate kinds}"
  , "# per-case seed = baseSeed + 1000003 * caseIndex, splitmix64 stream; inputs recorded explicitly below"
  , "# columns: id<TAB>kind<TAB>input<TAB>output  (s-expr grammar: compat/verdi/DiffHarness.lean)"
  , "# outputs are the Lean port's; `diffharness check` pins them (drift detection). The Rocq oracle"
  , "#   leg (compat/verdi/extraction/, extracted verdi-raft handlers) replays the input column and"
  , "#   byte-compares the output column: 280/280 match, 2026-08-10. Re-run it after regenerating." ]

def fixtureContent : Except String String := do
  let lines ← caseLines
  pure (String.intercalate "\n" (header ++ lines) ++ "\n")

/-! ## Driver -/

def firstDiff (a b : List String) : Nat × String × String :=
  let rec go (i : Nat) : List String → List String → Nat × String × String
    | [], [] => (i, "<end>", "<end>")
    | x :: _, [] => (i, x, "<missing>")
    | [], y :: _ => (i, "<missing>", y)
    | x :: xs, y :: ys => if x == y then go (i + 1) xs ys else (i, x, y)
  go 0 a b

def usage : String :=
  "usage: diffharness generate <path> | diffharness check <path>\n" ++
  "unknown arguments are an error (fail closed), not ignored"

end VerdiCompat.DiffHarness

open VerdiCompat.DiffHarness in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["generate", path] =>
    match fixtureContent with
    | .error e => IO.eprintln s!"diffharness: FAIL: {e}"; return 1
    | .ok content =>
      IO.FS.writeFile path content
      IO.println s!"diffharness: wrote {path} ({kinds.length * casesPerKind} cases)"
      return 0
  | ["check", path] =>
    match fixtureContent with
    | .error e => IO.eprintln s!"diffharness: FAIL: {e}"; return 1
    | .ok content =>
      if !(← System.FilePath.pathExists path) then
        IO.eprintln s!"diffharness: FAIL: no fixture recorded at {path} — a run that checked nothing must not pass; run `diffharness generate` and commit the result"
        return 1
      let file ← IO.FS.readFile path
      if file == content then
        IO.println s!"diffharness: OK: {path} matches regenerated output ({kinds.length * casesPerKind} cases)"
        return 0
      else
        let (i, got, want) := firstDiff (file.splitOn "\n") (content.splitOn "\n")
        IO.eprintln s!"diffharness: FAIL: {path} diverges from regenerated output at line {i + 1}:"
        IO.eprintln s!"  recorded:    {got}"
        IO.eprintln s!"  regenerated: {want}"
        return 1
  | _ =>
    IO.eprintln usage
    return 2
