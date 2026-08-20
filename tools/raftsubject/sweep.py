#!/usr/bin/env python3
"""sweep.py — the TRACKED liveness sweep: first order, then behind the sinks.

WHY THIS EXISTS.  `reachability.py` answers "is this quarantined declaration
reachable?" over ONE exported wire.  On that wire a quarantined declaration is
a SINK — it has no body, so its own callees are invisible — and the raft
subject tree has sinks high on every path (`newRaft`, `stepLeader`,
`(*raft).Step`, `Changer.EnterJoint`).  A first-order census therefore
UNDER-reports liveness, and the under-report is not a rounding error: six of
the twenty-six live declarations hide behind one of those four —
`Config.validate`, `DescribeConfChange`, `readOnly.recvAck`,
`readOnly.heartbeatCtx`, `Changer.apply`, `checkInvariants`.

So the headline number — "how many quarantined declarations must lower before
a RawNode-driven twin runs" — is the union of:

  PASS 1  the walk's work tree (frontier.py + the tracked plan), exported and
          censused.  Sound for `dead`, under-reports LIVE.
  PASS 2  the same tree with (a) every declaration still BELIEVED dead
          neutralised and (b) every live CAUSE flattened, so the sinks open and
          the walk continues through them.  Re-exported and re-censused, TO A
          FIXPOINT: neutralising a declaration cuts its own edges, so one
          round's dead set is the next round's blind spot, and stopping after
          one round is how a hand-curated dead list becomes self-confirming.
  the G-1 probe  the one declaration BOTH passes mask (below).

All three run here from tracked inputs only, and the union is printed as the
headline.  This file replaces the untracked `artifacts/patch2.py` the W2.2
sweep originally used (audit finding: the headline was not reproducible from
tracked material, and patch2 read its dead set from a hand-written file).
`artifacts/mksweep.py`, its companion, has no successor and needs none — it
built a scratch tree out of `deps/raft` before the root package was vendored;
`raftsubject/` is that tree now.

    tools/raftsubject/sweep.py [--frontend F] [--out DIR] [--plan P] [--tree T]

THE CLOSURE CHECK, which is the point of the last section of the report.
"Behind the sinks there is nothing new" is only a finding if no sinks are LEFT.
So the run ends by asking the final probe wire which declarations are still
quarantined AND reachable, and prints them by name and cause.  An empty list is
the claim; a non-empty one says exactly how far short the census fell.

PROBE ARTEFACT, LOUDLY.  Nothing PASS 2 writes is a proposal for the subject
tree.  The flattening swaps real calls for stand-ins and drops real mutex
operations; the resulting tree is WRONG as Go and is only ever asked one
question — "what does the call graph look like with these sinks open".  It
never touches `raftsubject/`.  Note that the stand-ins take the SAME arguments
as the calls they replace, because argument evaluation is itself an edge
(`Infof(..., DescribeConfChange(cc), ...)` is why that rendering path is live).

THE MASKING LIMIT, stated because it bounds the headline.  A declaration whose
FIRST refusal is flattened here reveals its SECOND (that is the point), but a
declaration the walk's own probe deltas REPLACED THE BODY OF is invisible to
both passes.  Exactly one is: `(*lockedRand).Intn`, whose body cannot survive
dropping the `crypto/rand` import that H-9 refuses on.  It is censused
separately, by putting the method verbatim in a SINGLE-package program where
H-9 does not fire (`specInitOrder` returns early below two units), and the
refusal that comes back is the real one.  Any future probe delta that replaces
a BODY owes the same treatment; `$drop-import` and `$rewrite` deltas do not.
"""

import argparse
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))

_spec = importlib.util.spec_from_file_location("frontier",
                                               os.path.join(HERE, "frontier.py"))
frontier = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(frontier)
_spec2 = importlib.util.spec_from_file_location("reachability",
                                                os.path.join(HERE, "reachability.py"))
reachability = importlib.util.module_from_spec(_spec2)
_spec2.loader.exec_module(reachability)

# The RawNode-driven twin's API surface (design note §2: the event vocabulary
# plus the storage the driver owns).  Every liveness verdict is relative to it.
ENTRIES = [
    "raft.NewRawNode", "raft.RawNode.Tick", "raft.RawNode.Step",
    "raft.RawNode.HasReady", "raft.RawNode.Ready", "raft.RawNode.Advance",
    "raft.RawNode.Propose", "raft.RawNode.Campaign",
    "raft.RawNode.ApplyConfChange", "raft.RawNode.ProposeConfChange",
    "raft.NewMemoryStorage", "raft.MemoryStorage.SetHardState",
    "raft.MemoryStorage.Append", "raft.MemoryStorage.CreateSnapshot",
    "raft.IsEmptyHardState", "raft.IsEmptySnap",
]

# Quarantined entries whose recvType starts with one of these is an IMPORTED
# stdlib declaration-only stub — the pre-existing contract, not a raft gap.
IMPORTED_PREFIXES = ("bytes.", "strings.", "sync.", "math/", "crypto/",
                     "encoding/", "sort.", "slices.", "time.", "io.", "os.",
                     "log.", "fmt.", "errors.", "context.", "unicode/",
                     "strconv.", "reflect.")

# The error constructor, kept separate because the `raft` package already gets
# one from the walk's own tracked probe file (probe/errors_new.go).  Pointer
# identity is preserved, so `err == ErrCompacted` still discriminates — the
# property raft actually reads off an error (log §2.4).
PROBE_ERRORS = """
type goleanProbeErrorString struct{ s string }

func (e *goleanProbeErrorString) Error() string { return e.s }

func goleanProbeErrorsNew(text string) error { return &goleanProbeErrorString{s: text} }
"""

# Every stand-in takes the SAME arguments as the call it replaces (variadic
# `...any` where the original was variadic), so the arguments are still
# evaluated and the call-graph edges through them survive.
PROBE_HELPERS = """package %s

// PROBE helpers (sweep measurement only; see sweep.py).  Not Go anyone should
// run: the returned values are placeholders.  Only the CALL GRAPH is asked of
// this tree.

func goleanProbeSprintf(format string, v ...any) string { return "sweep" }

func goleanProbeSprint(v ...any) string { return "sweep" }

func goleanProbeErrorf(format string, v ...any) error {
	return goleanProbeErrorsNew("sweep")
}

func goleanProbeFprint(w any, v ...any) (int, error) { return 0, nil }

func goleanProbeJoin(elems []string, sep string) string { return "sweep" }

func goleanProbeBytesEqual(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func goleanProbeLEUint64(b []byte) uint64 {
	var v uint64
	for i := 7; i >= 0; i-- {
		v = v<<8 | uint64(b[i])
	}
	return v
}

func goleanProbeLEPutUint64(b []byte, v uint64) {
	for i := 0; i < 8; i++ {
		b[i] = byte(v)
		v >>= 8
	}
}
"""


def run_frontend(fe, tree, out):
    r = subprocess.run([fe, "--dir", tree, "--out", out],
                       capture_output=True, text=True)
    return r.returncode, r.stderr.strip()


def census(wire_path):
    """(quarantined subject decls, quarantined imported stubs) off a wire."""
    wire = json.load(open(wire_path))
    subject, imported = {}, {}
    for f in wire.get("funcs", []):
        if "unsupported" in f:
            subject[f["name"]] = f["unsupported"]
    for m in wire.get("methods", []):
        if "unsupported" not in m:
            continue
        name = "%s.%s" % (m.get("recvType"), m.get("name"))
        (imported if name.startswith(IMPORTED_PREFIXES) else subject)[name] = m["unsupported"]
    return subject, imported


def liveness(wire_path, names):
    _, bodies, _ = reachability.load(wire_path)
    pred = reachability.reach(bodies, ENTRIES)
    return {n: reachability.path_of(pred, n) for n in names if n in pred}


def locate(tree, qualified):
    """`pkg.Type.Method` / `pkg.Func` -> the file declaring it, or None.

    Computed by scanning, never tabulated: a hardcoded name->file map is the
    thing that rots when upstream moves a declaration, and it would rot
    SILENTLY (a missing entry just skips a neutralisation).
    """
    parts = qualified.split(".")
    pkg, decl = parts[0], ".".join(parts[1:])
    d = os.path.join(tree, pkg)
    if not os.path.isdir(d):
        return None
    for f in sorted(os.listdir(d)):
        if not f.endswith(".go"):
            continue
        p = os.path.join(d, f)
        if frontier.find_decl(open(p).read(), decl) is not None:
            return p
    return None


def flatten(tree, dead):
    """PASS-2 tree surgery: neutralise the dead, flatten the live causes."""
    skipped = []
    for name in sorted(dead):
        p = locate(tree, name)
        if p is None:
            # A promoted stub (MemoryStorage.Lock/TryLock/Unlock) has no source
            # declaration to neutralise; it is the G-6 cause seen from the
            # method-set side and the mutex flattening below covers it.
            skipped.append(name)
            continue
        frontier.neutralise(p, ".".join(name.split(".")[1:]))

    # EVERY cause that quarantines a declaration on a live path is flattened —
    # not just the ones a previous run happened to need.  A cause left standing
    # keeps its declarations as sinks, and a sink is precisely what this pass
    # exists to remove; the residual-sink report at the end is the check that
    # nothing was forgotten.
    #
    # The replacement is of the call HEAD ONLY, never the whole call.  Two
    # reasons, and the second is the load-bearing one:
    #   * replacing `fmt.Sprintf(...)` with a constant orphans whatever the
    #     arguments used, so the tree stops type-checking (`declared and not
    #     used: c`) and the sweep would have to guess its way out;
    #   * ARGUMENT EVALUATION IS AN EDGE.  `stepLeader` calls
    #     `DescribeConfChange(cc)` as an ARGUMENT to `Infof`, and Go evaluates
    #     it whatever the callee does — which is exactly why that rendering
    #     path is live (log §2.3).  Dropping the arguments would delete the
    #     edge the sweep exists to find.
    counts = {}
    for root, _, files in os.walk(tree):
        for f in files:
            if not f.endswith(".go") or f.startswith("probe_"):
                continue
            p = os.path.join(root, f)
            s = old = open(p).read()
            for call, repl in (
                ("fmt.Sprintf", "goleanProbeSprintf"),
                ("fmt.Sprint", "goleanProbeSprint"),
                ("fmt.Errorf", "goleanProbeErrorf"),
                ("fmt.Fprintf", "goleanProbeFprint"),
                ("fmt.Fprint", "goleanProbeFprint"),
                ("strings.Join", "goleanProbeJoin"),
                ("bytes.Equal", "goleanProbeBytesEqual"),
                # G-2 inside function BODIES.  The walk plan leaves these alone
                # on purpose (so the census reports what errors.New costs); the
                # sweep must not, or Changer.{EnterJoint,LeaveJoint,Simple} and
                # (*raft).Step stay sinks and everything behind them is invisible.
                ("errors.New", "goleanProbeErrorsNew"),
                # G-8, the two read_only.go sites.
                ("binary.LittleEndian.Uint64", "goleanProbeLEUint64"),
                ("binary.LittleEndian.PutUint64", "goleanProbeLEPutUint64"),
            ):
                n = s.count(call + "(")
                if n:
                    s = s.replace(call + "(", repl + "(")
                    counts[call] = counts.get(call, 0) + n
            if s != old:
                open(p, "w").write(s)

    for pkg in sorted(os.listdir(tree)):
        d = os.path.join(tree, pkg)
        if not os.path.isdir(d):
            continue
        # `raft` already carries the walk's own probe file for the error ctor.
        body = PROBE_HELPERS % pkg
        if pkg != "raft":
            body += PROBE_ERRORS
        open(os.path.join(d, "probe_helpers.go"), "w").write(body)

    p = os.path.join(tree, "raft", "storage.go")
    s, n = re.subn(r"^(\t+)(defer )?ms\.(Lock|Unlock|TryLock)\(\)$",
                   r"\1_ = 0 // sweep: promoted mutex op dropped",
                   open(p).read(), flags=re.M)
    counts["promoted mutex op"] = n
    open(p, "w").write(s)
    return counts, skipped


def drain_imports(fe, tree, out, limit=60):
    """Ask the frontend which imports the flattening orphaned; never predict."""
    dropped = 0
    for _ in range(limit):
        rc, err = run_frontend(fe, tree, out)
        if rc == 0:
            return dropped, None
        # Both spellings go/types uses: `"p" imported and not used` and, for an
        # aliased import, `"p" imported as pb and not used`.
        m = re.search(r'type-check: (\S+?):\d+:\d+: "([^"]+)" imported '
                      r'(?:as \w+ )?and not used', err)
        if not m:
            return dropped, err
        path, pkg = m.group(1), m.group(2)
        s = open(path).read()
        s, n = re.subn(r'^\t(\w+ )?"%s"\n' % re.escape(pkg), "", s, count=1, flags=re.M)
        if not n:
            s, n = re.subn(r'^import (\w+ )?"%s"\n' % re.escape(pkg), "", s, count=1, flags=re.M)
        if not n:
            return dropped, "cannot drop import %s from %s" % (pkg, path)
        open(path, "w").write(s)
        dropped += 1
    return dropped, "import drain did not converge"


G1_PROBE = '''package main

// The G-1 probe: `(*lockedRand).Intn` verbatim from raft.go:93-104, in a
// SINGLE-package program.  H-9 (the inittask double-escape) only fires at two
// or more packages (`specInitOrder` returns early below two units), so this is
// the one place the frontend gets far enough to say what the election-jitter
// draw itself costs.  See sweep.py's masking-limit note.

import (
	"crypto/rand"
	"math/big"
	"sync"
)

type lockedRand struct {
	mu sync.Mutex
}

func (r *lockedRand) Intn(n int) int {
	r.mu.Lock()
	v, _ := rand.Int(rand.Reader, big.NewInt(int64(n)))
	r.mu.Unlock()
	return int(v.Int64())
}

var globalRand = &lockedRand{}

func main() { println(globalRand.Intn(10)) }
'''


def g1_probe(fe, out):
    d = os.path.join(out, "g1")
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    open(os.path.join(d, "main.go"), "w").write(G1_PROBE)
    wire = os.path.join(out, "g1.json")
    rc, err = run_frontend(fe, d, wire)
    if rc != 0:
        sys.exit("sweep.py: the G-1 probe did not export: %s" % err)
    subject, _ = census(wire)
    for name, why in subject.items():
        if name.endswith("lockedRand.Intn"):
            return why
    sys.exit("sweep.py: the G-1 probe exported with lockedRand.Intn NOT "
             "quarantined — crypto/rand is modeled now; retire G-1's row")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--frontend", default=os.path.join(REPO, "artifacts", "nativefrontend"))
    ap.add_argument("--plan", default=os.path.join(HERE, "frontier-plan.tsv"))
    ap.add_argument("--tree", default=os.path.join(REPO, "raftsubject"))
    ap.add_argument("--out", default=os.path.join(REPO, "artifacts", "sweep"))
    args = ap.parse_args()

    if not os.path.exists(args.frontend):
        sys.exit("sweep.py: no frontend at %s (build it first)" % args.frontend)
    os.makedirs(args.out, exist_ok=True)

    # ---- PASS 1 ------------------------------------------------------------
    work = os.path.join(args.out, "pass1")
    shutil.rmtree(work, ignore_errors=True)
    shutil.copytree(args.tree, work, ignore=shutil.ignore_patterns("README.md"))
    shutil.copy(os.path.join(HERE, "probe-main.go"), os.path.join(work, "main.go"))
    for ln in open(args.plan):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        row = ln.split("\t")
        if row[1] == "*":
            break
        frontier.apply_step(work, row[0], row[1], row[3] if len(row) > 3 else None)
    wire1 = os.path.join(args.out, "pass1.json")
    rc, err = run_frontend(args.frontend, work, wire1)
    if rc != 0:
        sys.exit("sweep.py: PASS 1 did not export cleanly — the plan is stale "
                 "against this frontend.  Run frontier.py to see where.\n%s" % err)
    subject1, imported1 = census(wire1)
    live1 = liveness(wire1, subject1)
    dead1 = sorted(set(subject1) - set(live1))

    # ---- PASS 2, TO A FIXPOINT ---------------------------------------------
    #
    # Opening the sinks means neutralising the declarations believed dead (a
    # panic body lowers, so the walk continues past them) and flattening the
    # live causes.  But neutralising a declaration CUTS ITS OWN EDGES, so a
    # declaration reachable only THROUGH a believed-dead one stays invisible —
    # and the belief came from PASS 1, which under-reports.  One pass is
    # therefore not enough, and taking its answer as final is how a hand-curated
    # dead list becomes self-confirming (the untracked `artifacts/patch2.py`
    # this replaces read its dead set from a file, which is exactly that trap).
    #
    # So iterate: each round neutralises only what is STILL believed dead, and
    # any declaration that turns out reachable is removed from the belief for
    # the next round.  The live set grows monotonically and is bounded by the
    # census, so this terminates; it stops when a round reveals nothing new.
    live = dict(live1)
    counts, skipped, dropped, rounds = {}, [], 0, 0
    while True:
        rounds += 1
        work2 = os.path.join(args.out, "pass2")
        shutil.rmtree(work2, ignore_errors=True)
        shutil.copytree(work, work2)
        counts, skipped = flatten(work2, sorted(set(subject1) - set(live)))
        wire2 = os.path.join(args.out, "pass2.json")
        dropped, err = drain_imports(args.frontend, work2, wire2)
        if err:
            sys.exit("sweep.py: PASS 2 round %d did not export cleanly: %s"
                     % (rounds, err))
        subject2, _ = census(wire2)
        # The QUERY SET is PASS 1's, not PASS 2's: PASS 2 gives the believed-dead
        # declarations panic bodies, so they lower and drop out of PASS 2's own
        # census.  Asking PASS 2 "what is quarantined AND reachable" would answer
        # "nothing" — an artefact of the surgery, not a finding.
        found = liveness(wire2, set(subject1) | set(subject2))
        new = {n: p for n, p in found.items() if n not in live}
        if not new:
            break
        live.update(new)
        if rounds > 20:
            sys.exit("sweep.py: PASS 2 did not reach a fixpoint in 20 rounds")
    revealed = {n: p for n, p in live.items() if n not in live1}

    # THE CLOSURE CHECK.  "Behind the sinks there is nothing new" is only a
    # finding if there are no sinks LEFT.  A declaration still quarantined in
    # the final PASS-2 wire AND reachable there is a sink the flattening did not
    # open, and everything behind it is unmeasured — so it is reported, by name
    # and by cause, instead of being folded silently into the headline.
    residual = {n: subject2[n] for n in liveness(wire2, subject2)}

    # ---- report ------------------------------------------------------------
    print("# sweep.py — frontend %s" % args.frontend)
    print("# entries: %s" % ", ".join(ENTRIES))
    print()
    print("PASS 1 (the walk's tree): %d quarantined subject declarations, "
          "%d imported stdlib stubs" % (len(subject1), len(imported1)))
    print("        %d LIVE, %d dead" % (len(live1), len(dead1)))
    for n in sorted(live1):
        print("  LIVE %-42s %s" % (n, live1[n]))
    print()
    print("PASS 2 (sinks opened, %d rounds to fixpoint): flattened %s; %d "
          "believed-dead declarations neutralised in the last round (%d had no "
          "source decl: %s); %d orphaned imports drained"
          % (rounds, ", ".join("%s x%d" % (k, v) for k, v in sorted(counts.items())),
             len(subject1) - len(live) - len(skipped), len(skipped),
             ", ".join(skipped) or "-", dropped))
    print("        %d NEWLY live behind the PASS-1 sinks" % len(revealed))
    for n in sorted(revealed):
        print("  LIVE %-42s %s" % (n, revealed[n]))
    print()
    if residual:
        print("RESIDUAL SINKS: %d declarations are still quarantined AND "
              "reachable in the final PASS-2 wire — whatever they call is "
              "UNMEASURED, so the census is not closed:" % len(residual))
        for n in sorted(residual):
            print("  sink %-42s %s" % (n, residual[n][:120]))
    else:
        print("RESIDUAL SINKS: none — every reachable declaration in the final "
              "PASS-2 wire has a body, so the census is CLOSED over this tree "
              "(nothing is hidden behind a refusal).")
    print()
    print("G-1 probe (masked in both passes, censused standalone):")
    print("  LIVE raft.lockedRand.Intn                       %s" % g1_probe(args.frontend, args.out))
    print()
    print("HEADLINE: %d LIVE quarantined subject declarations "
          "(%d first-order + %d behind sinks + 1 masked G-1) out of %d "
          "quarantined in PASS 1, plus %d imported stdlib stubs that are the "
          "declaration-only-stub contract and not a raft gap."
          % (len(live) + 1, len(live1), len(revealed), len(subject1),
             len(imported1)))


if __name__ == "__main__":
    main()
