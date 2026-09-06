package main

// Unit tests for the method-set record CLASSIFIER (emit.go,
// methodSetCoverageForKind — class closure of BUG-053, contract note
// docs/2026-08-10_method-set-record-contract.md §3). The S6 audit
// found the original inline switch failed OPEN (`default: full` — an
// unknown/absent def.kind inherited the strongest coverage, the
// retired blanket-true arm relocated to the emitter); these pins make
// a re-introduction of that shape visible forever: every known kind's
// classification is pinned, and the unknown/empty/nameless shapes
// must REFUSE the export, never mint a record.

import "testing"

func TestMethodSetCoverageKnownKinds(t *testing.T) {
	cases := []struct {
		kind     string
		coverage string
		carrier  bool
	}{
		{"struct", "full", true},
		{"defined", "full", true},
		{"unsupported", "exported", true},
		{"interface", "", false},
		{"alias", "", false},
	}
	for _, c := range cases {
		coverage, carrier, err := methodSetCoverageForKind("main.T", c.kind)
		if err != nil {
			t.Fatalf("kind %q: unexpected refusal: %v", c.kind, err)
		}
		if carrier != c.carrier || coverage != c.coverage {
			t.Fatalf("kind %q: got (%q, %v), want (%q, %v)",
				c.kind, coverage, carrier, c.coverage, c.carrier)
		}
	}
}

func TestMethodSetCoverageUnknownKindRefuses(t *testing.T) {
	// The BUG-053-class negative: an unknown kind must fail the export
	// (no record, no error-free return) — never classify as `full`.
	for _, kind := range []string{"widget", "generic", "Struct"} {
		coverage, carrier, err := methodSetCoverageForKind("main.T", kind)
		if err == nil {
			t.Fatalf("kind %q: classified (%q, %v) instead of refusing",
				kind, coverage, carrier)
		}
	}
}

func TestMethodSetCoverageEmptyKindRefuses(t *testing.T) {
	// kind "" is what an absent or malformed `def` map yields through
	// the comma-ok extraction — the exact shape the audit flagged.
	if _, _, err := methodSetCoverageForKind("main.T", ""); err == nil {
		t.Fatal("empty kind (absent/malformed def) did not refuse")
	}
}

func TestMethodSetCoverageEmptyNameRefuses(t *testing.T) {
	// A nameless TypeDef must not mint a record keyed "".
	if _, _, err := methodSetCoverageForKind("", "struct"); err == nil {
		t.Fatal("empty TypeDef name did not refuse")
	}
}
