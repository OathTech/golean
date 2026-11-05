package main

// initreach_test.go — H-11's init reach walk (emit.go checkInitQuarantine)
// at BUG-401's fix round, 2026-11-05: the stdlib shim's RUNTIME-refusal
// helper (stdlibshim.go shimRuntimeRefusalReasons) is a run-time STOP, not
// an unmodeled callee — an initializer that reaches it statically exports
// and the helper's own stub stays force-quarantined (BUG-154: a call still
// throws the unrecoverable stop); a genuinely quarantined callee reached
// from $pkginit still refuses the whole export, beside the helper or not.
// The corpus rows fmt/sweep-s21-init-* pin the observable contract.

import (
	"fmt"
	"strings"
	"testing"
)

func TestInitReachPassesOverShimRefusalHelper(t *testing.T) {
	call := func(callee string) map[string]any { return map[string]any{"expr": "call", "func": callee} }
	stop := map[string]any{"name": shimUnsupportedName, "unsupported": shimRuntimeRefusalReasons[shimUnsupportedName]}
	bad := map[string]any{"name": "bad", "unsupported": "frontend-quarantined: an unmodeled callee"}
	quoter := map[string]any{"name": "goleanShimFmtQuoteString", "body": call(shimUnsupportedName)}
	t.Run("direct", func(t *testing.T) {
		if err := checkInitQuarantine([]any{map[string]any{"name": "$pkginit", "body": call(shimUnsupportedName)}, stop}, nil); err != nil {
			t.Fatalf("the shim's run-time stop refused the export: %v", err)
		}
	})
	t.Run("through-a-shim-body", func(t *testing.T) {
		if err := checkInitQuarantine([]any{map[string]any{"name": "$pkginit", "body": call("goleanShimFmtQuoteString")}, quoter, stop}, nil); err != nil {
			t.Fatalf("a shim body's refusal arm refused the export: %v", err)
		}
	})
	t.Run("a-quarantined-callee-still-refuses", func(t *testing.T) {
		err := checkInitQuarantine([]any{map[string]any{"name": "$pkginit", "body": call("helper")}, map[string]any{"name": "helper", "body": call("bad")}, bad}, nil)
		if err == nil || !strings.Contains(err.Error(), "reaches quarantined function bad (frontend-quarantined: an unmodeled callee)") {
			t.Fatalf("a quarantined callee must refuse the export by name: %v", err)
		}
	})
	t.Run("beside-the-helper", func(t *testing.T) {
		body := map[string]any{"stmt": "block", "body": []any{call(shimUnsupportedName), call("bad")}}
		err := checkInitQuarantine([]any{map[string]any{"name": "$pkginit", "body": body}, stop, bad}, nil)
		if err == nil || !strings.Contains(err.Error(), "reaches quarantined function bad") {
			t.Fatalf("the helper beside a quarantined callee must not hide it: %v", err)
		}
	})
}

// The seven shapes of BUG-401 end to end: the export passes, the refusal
// helper is reached from $pkginit (the walk passed over it rather than
// never meeting it), and its stub is still the force-quarantined stop.
func TestFmtDesugarAtInitExports(t *testing.T) {
	preamble := "package main\n\nimport \"fmt\"\n\ntype st int\n\nfunc (st) String() string { return \"st\" }\n\nfunc r() string { return g }\n\nfunc main() { r() }\n\n"
	for name, decls := range map[string]string{
		"sprint-initializer":     "var g = fmt.Sprint(\"x\", 1)\n",
		"sprintln-in-init":       "var g string\n\nfunc init() { g = fmt.Sprintln(\"i\", 3) }\n",
		"spread-sprintf-in-init": "var g string\n\nfunc init() {\n\tf := func(v ...any) string { return fmt.Sprintf(\"%d\", v...) }\n\tg = f(1)\n}\n",
		"q-initializer":          "var g = fmt.Sprintf(\"%q\", \"x\")\n",
		"v-stringer-initializer": "var g = fmt.Sprintf(\"%v\", st(1))\n",
		"s-error-initializer":    "var g = fmt.Sprintf(\"%s\", fmt.Errorf(\"e\"))\n",
		"sprint-indirect":        "var g = helper()\n\nfunc helper() string { return fmt.Sprint(\"x\", 1) }\n",
	} {
		t.Run(name, func(t *testing.T) {
			program, err := lowerDir(t, writeDir(t, map[string]string{"main.go": preamble + decls}))
			if err != nil {
				t.Fatalf("export refused: %v", err)
			}
			stub := findFunc(program, shimUnsupportedName)
			if stub == nil || !strings.Contains(fmt.Sprint(stub["unsupported"]), "RUNTIME refusal") {
				t.Fatalf("the refusal helper is not the force-quarantined stop (BUG-154): %v", stub)
			}
			if findFunc(program, "$pkginit") == nil {
				t.Fatal("no $pkginit: the initializer did not lower as init work")
			}
			called := map[string]bool{}
			collectCalledFuncs(program["funcs"], called)
			if !called[shimUnsupportedName] {
				t.Fatal("no emitted body references the refusal helper: the shape does not exercise the walk")
			}
		})
	}
}
