package main

import (
	"bytes"
	"fmt"
	"os"
	"regexp"
	"unicode/utf8"
)

// Paired evidence belongs to one completed run in a runner-owned directory.
// This validates a runtime channel, not arbitrary caller-forged capture files.
//
// The channel is MANDATORY (landing review 2026-09-07, auditor A finding R6,
// fixed [AGENT] per the coordinator's brief: "ok/race/abort must all require
// it uniformly"). The sprint's first cut accepted an empty ack + empty report
// pair and fell through to the raw-marker fallback, so a missing hook
// registration was silently a weaker check; ok/race already required the ack.
// Now every query that classifies stderr — ok, race, panic, fatal, deadlock,
// message, record — refuses by name when the channel is absent, unregistered,
// malformed, or (on an abort) empty. A pre-main abort (package initializer or
// init() panics before main's first statement installs the hook) therefore
// REFUSES rather than being classified from unauthenticated bytes; that red is
// the honest outcome until a ruled exception exists (there is none).
type crashEvidence struct {
	enabled bool
	report  []byte
	ack     []byte
}

type abortView struct {
	kind    string
	message []byte
	output  []byte
}

const crashAckText = "registered\n"

// dopanic_m's signal line, printed once after the chain and before the
// blank line + trace header: `[signal SIGSEGV: segmentation violation
// code=0x1 addr=0x0 pc=0x…]`. Anchored to the END of the pre-header region.
var signalLineRe = regexp.MustCompile(`\n\[signal [^\n]*\]\n\z`)

func readCrashEvidence(reportPath, ackPath string) (crashEvidence, error) {
	if reportPath == "" && ackPath == "" {
		return crashEvidence{}, nil
	}
	if reportPath == "" || ackPath == "" {
		return crashEvidence{}, fmt.Errorf("crash evidence: report and registration paths must be paired")
	}
	report, err := os.ReadFile(reportPath)
	if err != nil {
		return crashEvidence{}, fmt.Errorf("crash evidence: read report: %w", err)
	}
	ack, err := os.ReadFile(ackPath)
	if err != nil {
		return crashEvidence{}, fmt.Errorf("crash evidence: read registration: %w", err)
	}
	e := crashEvidence{true, report, ack}
	return e, e.validate()
}

// validate refuses every channel state other than "hook registered in this
// run". It says nothing about the report: the ok/race path requires it empty,
// the abort path requires it non-empty (checkedAbortView).
func (e crashEvidence) validate() error {
	if !e.enabled {
		return fmt.Errorf("crash evidence: required — no same-run --crash-report/--crash-registered pair was supplied; stderr classification without the runtime channel is refused")
	}
	if len(e.ack) == 0 {
		if len(e.report) != 0 {
			return fmt.Errorf("crash evidence: nonempty report without registration acknowledgement")
		}
		return fmt.Errorf("crash evidence: no hook registration acknowledgement — the oracle's _goleanSetupCrash never ran (the subject aborted before main's first statement, or the hook was not installed); an unauthenticated run is refused")
	}
	if !bytes.Equal(e.ack, []byte(crashAckText)) {
		return fmt.Errorf("crash evidence: malformed registration acknowledgement")
	}
	return nil
}

// originKind validates raw indentation BEFORE any decoding/normalization.
// Payload newlines acquire TAB in printindented. With an owned crash channel
// this distinguishes the actual first trace from a payload's fake header.
func originKind(report []byte) (string, error) {
	header := abortTraceHeaderRe.FindIndex(report)
	if header == nil {
		return "", fmt.Errorf("abort classification: missing trace header")
	}
	// Runtime chain shape (runtime/panic.go printpanics + printindented @
	// go1.26.5): every chain entry after the first is printed as
	// "\n\tpanic: …" and every payload newline is rendered "\n\t", so within
	// a runtime-written report every LF before the trace header is followed
	// by a TAB — except the single LF that ends the last chain line, and
	// except the ONE un-indented "[signal <name> code=… addr=… pc=…]" line
	// dopanic_m prints after the chain for a signal-induced panic (nil
	// dereference → SIGSEGV; measured on the corpus, 2026-09-07). A bare
	// "\npanic: "/"\nfatal error: " (or any other un-indented line) inside
	// the copy cannot come from the runtime: refused (landing review
	// 2026-09-07 [AGENT], found while making the channel mandatory).
	head := report[:header[0]]
	if m := signalLineRe.FindIndex(head); m != nil {
		head = head[:m[0]+1] // keep the LF that ended the last chain line
	}
	for i := 0; i+1 < len(head); i++ {
		if head[i] == '\n' && head[i+1] != '\t' {
			return "", fmt.Errorf("abort classification: un-indented continuation line inside the runtime report (printpanics/printindented TAB-indent every continuation) — not a runtime-written chain, refused")
		}
	}
	trace := report[header[0]:]
	if trace[0] == '\n' {
		trace = trace[1:]
	}
	kind, err := pinnedTraceKind(trace)
	if err != nil {
		return "", err
	}
	tail := report[header[1]:]
	if bytes.Contains(tail, []byte("panic: ")) || bytes.Contains(tail, []byte("fatal error: ")) ||
		bytes.Contains(tail, []byte("\nruntime stack:")) {
		return "", fmt.Errorf("abort classification: additional or unknown report boundary after selected origin, refused")
	}
	return kind, nil
}

func makeAbortView(kind string, report, output []byte) (abortView, error) {
	if !utf8.Valid(output) {
		return abortView{}, fmt.Errorf("stderr split: program output is not valid UTF-8, refused")
	}
	marker := []byte("panic: ")
	if kind == "fatal" {
		marker = []byte("fatal error: ")
	}
	if !bytes.HasPrefix(report, marker) {
		return abortView{}, fmt.Errorf("abort classification: %s origin without initial message marker, refused", kind)
	}
	message := bytes.SplitN(report[len(marker):], []byte{'\n'}, 2)[0]
	if kind == "fatal" && bytes.Equal(message, []byte("all goroutines are asleep - deadlock!")) {
		kind = "deadlock"
	}
	return abortView{kind, message, output}, nil
}

// checkedAbortView classifies an aborted run from its stderr AND the same-run
// crash channel. The channel copy must be the byte-identical suffix of stderr
// (minus go run's trailer); its first trace frame decides the terminal kind.
//
//   - panic: the runtime sets m.dying BEFORE printing the panic chain, so the
//     channel copy begins at `panic: ` and is the exact report; everything
//     before it is the program's own output.
//   - fatal/deadlock: `fatal error: <msg>` is printed BEFORE m.dying, so the
//     channel copy holds only the trace and the message line is NOT
//     authenticated. It is recovered from the raw bytes under a strict rule —
//     exactly one `fatal error: ` marker at a line start and no `panic: `
//     anywhere before the authenticated trace — and every other shape
//     (notably a fatal raised DURING panic unwinding, BUG-106) refuses.
//
// An exit-2 run whose channel copy is EMPTY is not a runtime abort at all
// (os.Exit(2), or a printed report): refused.
func checkedAbortView(stderr []byte, e crashEvidence) (abortView, error) {
	if err := e.validate(); err != nil {
		return abortView{}, err
	}
	if !bytes.HasSuffix(stderr, []byte("\nexit status 2\n")) {
		return abortView{}, fmt.Errorf("abort classification: expected the child's exact exit status 2 trailer")
	}
	// Strip ONLY go run's trailer; the preceding LF belongs to the report.
	body := stderr[:len(stderr)-len("exit status 2\n")]
	if len(e.report) == 0 {
		return abortView{}, fmt.Errorf("crash evidence: exit status 2 but the runtime wrote no crash report — not an authenticated runtime abort (os.Exit(2) or a printed report), refused")
	}
	if !bytes.HasSuffix(body, e.report) {
		return abortView{}, fmt.Errorf("crash evidence: report is not the entire byte-identical stderr suffix")
	}
	kind, err := originKind(e.report)
	if err != nil {
		return abortView{}, err
	}
	if kind == "panic" {
		return makeAbortView(kind, e.report, body[:len(body)-len(e.report)])
	}
	// fatal: the message precedes m.dying and is absent from the copy. The
	// bytes before the authenticated trace are recovered under the strict
	// rule above; EVERY raw marker counts, including LF TAB continuations
	// (the old exemption made print("panic: forged\n\t");panic("actual") a
	// false observation).
	head := body[:len(body)-len(e.report)]
	panics, fatals := bytes.Count(head, []byte("panic: ")), bytes.Count(head, []byte("fatal error: "))
	if panics != 0 || fatals != 1 {
		return abortView{}, fmt.Errorf("abort classification: ambiguous fatal message/output before m.dying (%d panic/%d fatal markers precede the authenticated trace), refused", panics, fatals)
	}
	start := bytes.Index(head, []byte("fatal error: "))
	if start != 0 && head[start-1] != '\n' {
		return abortView{}, fmt.Errorf("stderr split: raw report marker glued to program output, refused")
	}
	return makeAbortView(kind, body[start:], body[:start])
}

func observedOutput(stderr []byte, status string, e crashEvidence) ([]byte, error) {
	if err := e.validate(); err != nil {
		return nil, err
	}
	if status == "ok" || status == "race" {
		if len(e.report) != 0 {
			return nil, fmt.Errorf("crash evidence: %s run requires an empty crash report (the runtime wrote one)", status)
		}
		return splitNonAbortStderr(stderr, status)
	}
	view, err := checkedAbortView(stderr, e)
	if err != nil {
		return nil, err
	}
	if view.kind != status {
		return nil, fmt.Errorf("stderr split: actual %s report cannot be observed as %s", view.kind, status)
	}
	return view.output, nil
}
