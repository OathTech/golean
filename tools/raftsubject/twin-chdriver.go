// THE CHOICE-DRIVEN TWIN DRIVER — the ∀ch subject (campaign Arc 1).
//
// This is the program the T1 statement quantifies over (constitution
// §2.1): the same n=3 RawNode twin, the same S1–S3 per-step checker
// and S4 stopping condition as the schedule-driven battery
// (twin-lib.go) — but the DELIVERY ORDER is not an input schedule.
// Each round delivers ONE live message picked by ranging over a MAP
// of the live multiset indices: Go's own map-iteration latitude (the
// machine's `mapIter` choice site; spec#For_statements' range-over-map
// clause). "For ALL choice streams" in the statement therefore
// quantifies over exactly the delivery orders a conforming Go
// implementation may realize — the reliable-first envelope's
// unbounded-reordering axis, grounded in real language latitude
// rather than an artificial input. (The same mechanism as the
// certified miniature `multipkg/mini-raft-twin/choice-order`, at the
// real subject.)
//
// The client protocol is DETERMINISTIC, so the map pick is the only
// nondeterminism: campaign(1) once at the start; whenever the network
// is quiescent, propose the next pending command at node 1 (the
// drop-and-retry client — quiescence after the initial campaign
// implies an elected leader on the reliable network, so retries make
// progress); stop at S4 (all commands committed on every node, ≥1
// claim) or at the fuel bound (an HONEST incomplete: complete=0,
// never a claim). No drops, no duplication (reliable-first, §2.2.1);
// ticks are not driven (no jitter consumption — the D-11 seam stays
// closed, as in the schedule battery).
//
// Observation: the per-round trace is NOT part of the quantified
// claim (different orders legitimately produce different traces); the
// statement-facing observable is the END LINE — viol / claims /
// committed / complete / floor — plus the final projection. T1 says:
// every COMPLETING run has viol=0; the completion witness says some
// stream completes with the floor met.
package main

// runTwinChoice is the shared engine; the two entry points project it.
func runTwinChoice() (*twin, int, int) {
	installLogger()
	t := newTwin(3, 2)
	t.say("[choice-driven]\n")
	// Deterministic opening: node 1 campaigns (uncontended at n=3 on
	// the reliable network — its victory needs only delivery).
	t.step(op{kind: opCampaign, node: 1})
	const fuel = 400
	round := 0
	stuckPropose := 0
	for round = 0; round < fuel; round++ {
		// Rebuild the live-index map (slice walk: deterministic
		// content and insertion; the map's ITERATION is the latitude).
		live := map[int]bool{}
		for j := range t.net {
			if t.live[j] {
				live[j] = true
			}
		}
		if len(live) > 0 {
			// THE PICK: one map-range draw — the round's choice.
			picked := -1
			for j := range live {
				picked = j
				break
			}
			m := t.net[picked]
			t.say("r" + itoa(round+1) + " pick#" + itoa(picked) +
				" type" + itoa(int(m.GetType())) + "->" + utoa(m.GetTo()))
			t.deliverIdx(picked)
			t.say(" " + t.projection() + "\n")
			stuckPropose = 0
			continue
		}
		// Quiescent. S4?
		if t.complete() && len(t.pending) == 0 {
			break
		}
		if len(t.pending) > 0 {
			t.say("r" + itoa(round+1) + " ")
			t.step(op{kind: opPropose, node: 1})
			t.say("\n")
			stuckPropose++
			if stuckPropose > 3 {
				// Defensive: quiescent + repeatedly dropped should be
				// unreachable (quiescence after campaign(1) implies a
				// leader); an honest halt beats a silent spin.
				t.halt = true
				t.say("!driver: propose stuck at quiescence\n")
				break
			}
			continue
		}
		// Quiescent, nothing pending, S4 not met (e.g. a node lagging
		// with nothing in flight cannot happen on the reliable net —
		// defensively an honest stop).
		t.halt = true
		t.say("!driver: quiescent without S4\n")
		break
	}
	comp := 0
	if t.complete() && len(t.pending) == 0 && !t.halt {
		comp = 1
	}
	floorOK := 1
	if t.claims < 1 || t.committed < 1 {
		floorOK = 0
	}
	t.say("end viol=" + itoa(t.violations) + " claims=" + itoa(t.claims) +
		" committed=" + itoa(t.committed) + " complete=" + itoa(comp) +
		" floor=" + itoa(floorOK) + " rounds=" + itoa(round) + "\n")
	t.say("final " + t.projection() + "\n")
	return t, comp, floorOK
}

// probeTwinChoice — the INSTRUMENT entry: the full per-round trace.
func probeTwinChoice() string {
	t, _, _ := runTwinChoice()
	return t.trace
}

// twinChoiceVerdict — the STATEMENT entry (campaign Arc 1): the
// machine-readable observable the T1 theorem reads. Five integers:
// violations, claims, committed, complete, floor. T1 (constitution
// §2.1): for ALL choice streams and fuel, a completing run has
// violations = 0 — the in-program S1–S3 checker (twin-lib.go,
// checked at every apply/claim step; the §2.2 item-4 projection
// applies to the S2 comparison) recorded nothing, at any step. The
// completion witness: some stream completes with complete = 1 and
// floor = 1. Dumb on purpose: the observable is five ints, the
// checker is the harness's own, and everything else is proof-side.
func twinChoiceVerdict() (int, int, int, int, int) {
	t, comp, floorOK := runTwinChoice()
	return t.violations, t.claims, t.committed, comp, floorOK
}
