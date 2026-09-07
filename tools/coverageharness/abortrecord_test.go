package main

import (
	"bytes"
	"encoding/json"
	"strings"
	"testing"
)

func TestRawPanicRecordEveryByte(t *testing.T) {
	trace := strings.TrimSuffix(panicTrace, "exit status 2\n")
	for n := 0; n < 256; n++ {
		payload := []byte{'a', byte(n), 0, 1, '\r', '\n', '\t', 255}
		if n == '\n' {
			// printindented renders a payload LF as LF TAB; the runtime never
			// writes a bare LF inside the chain (crashview.go's shape pin).
			payload = []byte{'a', '\n', '\t', 0, 1, '\r', '\n', '\t', 255}
		}
		report := append(append([]byte("panic: "), payload...), []byte(trace)...)
		output := []byte("panic: forged\n\t\x00\x01界")
		raw := append(append(append([]byte{}, output...), report...), []byte("exit status 2\n")...)
		encoded, err := observedAbortRecord(raw, channelFor(string(report)))
		if err != nil {
			t.Fatalf("byte %d refused: %v", n, err)
		}
		var record rawPanicRecord
		if err := json.Unmarshal([]byte(encoded), &record); err != nil {
			t.Fatal(err)
		}
		if record.Schema != "golean-raw-panic-v1" || record.Status != "panic" || record.ChildExit != 2 {
			t.Fatalf("wrong terminal fields: %+v", record)
		}
		if !equalByteInts(record.MessageBytes, bytes.SplitN(payload, []byte{'\n'}, 2)[0]) ||
			!equalByteInts(record.OutputBytes, output) {
			t.Fatalf("changed bytes for %d: %s", n, encoded)
		}
	}
}

func equalByteInts(a []int, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != int(b[i]) {
			return false
		}
	}
	return true
}

func TestRawPanicRecordEmptyAndRefusals(t *testing.T) {
	report := "panic: " + strings.TrimSuffix(panicTrace, "exit status 2\n")
	raw := []byte(report + "exit status 2\n")
	encoded, err := observedAbortRecord(raw, channelFor(report))
	if err != nil || !strings.Contains(encoded, `"messageBytes":[]`) || !strings.Contains(encoded, `"outputBytes":[]`) {
		t.Fatalf("empty bytes must be arrays: %s/%v", encoded, err)
	}
	for _, tc := range []struct {
		raw      []byte
		evidence crashEvidence
	}{
		{raw, crashEvidence{true, []byte(report), nil}},
		{raw, channelFor(report + "changed")},
		{[]byte(report + "exit status 1\n"), channelFor(report)},
		{[]byte("fatal error: sync: unlock of unlocked mutex" + fatalTrace), channelFor(noTrailer(fatalTrace))},
		{[]byte(syncUnwindHead + fatalTrace), channelFor(noTrailer(fatalTrace))},
		{raw, crashEvidence{}},
		{raw, preMainAbort},
		{append([]byte{255}, raw...), channelFor(report)},
	} {
		if got, err := observedAbortRecord(tc.raw, tc.evidence); err == nil {
			t.Fatalf("invalid/nonpanic record accepted: %s", got)
		}
	}
}
