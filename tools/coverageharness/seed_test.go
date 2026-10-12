package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The seeded mode (seed.go; seeded-heap slice C, 2026-10-12). Three layers:
// the generator's refusals of the seed file's SHAPE and type spellings (by
// name, the classes GoLean/SeedFile.lean refuses); the argument tokens; and
// the generated oracle RUN under the pinned Go — the seed-relative pointer
// paths, the escape refusal (status unsupported, the text class of GoLean's
// seed readout refusal), the zero-size refusal, and the run-time typing
// refusals (status error, `seed: …`). Like the other go-run tests this
// execs `go run`; the ci runs the package with -count=1.

func TestSeedFileRefusals(t *testing.T) {
	cell := func(typ, value string) string {
		return `{"schema":"golean-seed-v1","cells":[{"type":"` + typ + `","value":` + value + `}]}`
	}
	for _, tc := range []struct{ name, file, want string }{
		{"float", cell("float64", "1"), "type spelling float64: a float type (float64) is not in golean-seed-v1"},
		{"string", cell("[2]string", "1"), "type spelling [2]string: string is not in golean-seed-v1"},
		{"byte", cell("byte", "1"), "byte (spell it uint8)"},
		{"uintptr", cell("*uintptr", "1"), "type spelling *uintptr: uintptr is not in golean-seed-v1"},
		{"slice", cell("[]int", "1"), "a slice type is not in golean-seed-v1"},
		{"map", cell("map[int]int", "1"), "a map type is not in golean-seed-v1"},
		{"chan", cell("chan int", "1"), "a channel type is not in golean-seed-v1"},
		{"chan-keyword", cell("chan", "1"), "a channel type is not in golean-seed-v1"},
		{"sync", cell("sync.Mutex", "1"), "a sync type is not in golean-seed-v1"},
		{"qualified", cell("main.Node", "1"), "a package-qualified type"},
		{"anon-struct", cell("struct{x int}", "1"), "an anonymous struct type is not in golean-seed-v1"},
		{"array-len", cell("[03]int", "1"), "array length 03 is not a decimal nat"},
		{"reserved", cell("_goleanX", "1"), "reserved for the harness"},
		{"frac", cell("int", "1.5"), "number 1.5: a fraction or exponent is not allowed"},
		{"expo", cell("int", "1e2"), "number 1e2: a fraction or exponent is not allowed"},
		{"neg-zero", cell("uint8", "-0"), "number -0: a negative zero is not a golean-seed-v1 integer"},
		{"neg-zero-signed", cell("[2]int", "[1,-0]"), "number -0: a negative zero is not a golean-seed-v1 integer"},
		{"null", cell("*int", "null"), "null is not a seed value"},
		{"str", cell("int", `"x"`), "a string is not a seed value"},
		{"nil-false", cell("*int", `{"nil":false}`), "seed.cells[0].value.nil: expected true"},
		{"ref-extra", cell("*int", `{"ref":{"cell":0,"path":[]},"x":1}`), "a struct with a field named ref or nil is not expressible in golean-seed-v1"},
		{"ref-cell", cell("*int", `{"ref":{"cell":-1,"path":[]}}`), "cell: expected a nat"},
		{"ref-path", cell("*int", `{"ref":{"cell":0,"path":[true]}}`), "a path element is a field name (string) or an index (nat)"},
		{"extra-key", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":1,"x":2}]}`, "seed.cells[0]: expected exactly keys"},
		{"dup-key", `{"schema":"golean-seed-v1","schema":"golean-seed-v1","cells":[]}`, `duplicate JSON object key "schema"`},
		{"schema", `{"schema":"golean-seed-v2","cells":[]}`, "seed.schema: expected"},
		{"trailing", `{"schema":"golean-seed-v1","cells":[]} 1`, "trailing data"},
		{"surrogate", cell("Node", `{"\ud83d\ude00":1}`), "surrogate escape"},
		{"utf8", "{\"schema\":\"golean-seed-v1\",\"cells\":[{\"type\":\"\xff\",\"value\":1}]}", "not valid UTF-8"},
	} {
		_, err := parseSeedFile([]byte(tc.file))
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: parseSeedFile(%s) = %v; want a refusal naming %q", tc.name, tc.file, err, tc.want)
		}
	}
	cells, err := parseSeedFile([]byte(`{"schema":"golean-seed-v1","cells":[{"type":"Node","value":{"next":{"ref":{"cell":1,"path":[]}},"val":2}},{"type":"[2]*Node","value":[{"nil":true},{"ref":{"cell":0,"path":[]}}]}]}`))
	if err != nil || len(cells) != 2 || cells[0].typ != "Node" || cells[1].typ != "[2]*Node" {
		t.Fatalf("a valid two-cell seed: %v, %v", cells, err)
	}
}

func TestSeedArgTokens(t *testing.T) {
	args, err := parseSeedArgs("ref:0,ref:12.a[3].b,nil,-5,18446744073709551615")
	if err != nil || len(args) != 5 {
		t.Fatalf("parseSeedArgs: %v %v", args, err)
	}
	if args[1].cell != 12 || goPathLiteral(args[1].path) != `[]any{"a", 3, "b"}` || args[2].kind != 'n' || args[3].lit != "-5" {
		t.Fatalf("parsed tokens: %+v", args)
	}
	for _, bad := range []string{"ref:", "ref:01", "ref:0.", "ref:0[x]", "ref:0[01]", "ref:0._", "Nil", "ref:0,,nil", "1.5"} {
		if _, err := parseSeedArgs(bad); err == nil {
			t.Errorf("parseSeedArgs(%q) accepted a malformed token", bad)
		}
	}
}

const seedFixture = `package main

type Node struct {
	next *Node
	val  int
}

type Pair struct {
	a [3]int
	b bool
}

type Z struct{}

type B struct {
	_ int
	x int
}

func next(n *Node) *Node { return n.next }

func elem(p *Pair) *int { return &p.a[2] }

func retLocal(p *int) *int {
	x := *p
	return &x
}

func leak(q **int) int {
	x := 1
	*q = &x
	return x
}

func zp(z *Z) *Z { return z }

func val(n *Node) int { return n.val }

func inc(p *int) int {
	*p++
	return *p
}

func useB(b *B) int { return b.x }

func take(n Node) int { return n.val }

// P and PA: a NAMED pointer type and an ALIAS of one (review MEDIUM-1): a
// ref/nil argument binds at both, as on the machine.
type P *int

type PA = *int

func viaNamed(p P) int {
	if p == nil {
		return -1
	}
	*p = *p + 1
	return *p
}

func viaAlias(p PA) int {
	if p == nil {
		return -2
	}
	*p = *p * 2
	return *p
}

func main() {}
`

// seededOracle generates the seeded oracle for subject over the seed file
// text and runs it; generation errors are returned, a run's stdout is.
func seededOracle(t *testing.T, subject, args, seed string) (string, error) {
	t.Helper()
	root := t.TempDir()
	input := filepath.Join(root, "input")
	if err := os.Mkdir(input, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(input, "main.go"), []byte(seedFixture), 0o644); err != nil {
		t.Fatal(err)
	}
	seedPath := filepath.Join(root, "seed.json")
	if err := os.WriteFile(seedPath, []byte(seed), 0o644); err != nil {
		t.Fatal(err)
	}
	oracle := filepath.Join(root, "oracle")
	if err := run(config{input: filepath.Join(input, "main.go"), out: oracle, subject: subject, args: args, status: "ok", seed: seedPath}); err != nil {
		return "", err
	}
	r := goRunOracle(t, oracle)
	if len(r.stderr) != 0 || r.exit != 0 {
		t.Fatalf("%s: the seeded oracle did not exit cleanly: exit %d, stderr %s", subject, r.exit, r.stderr)
	}
	return string(r.stdout), nil
}

const cycleSeed = `{"schema":"golean-seed-v1","cells":[{"type":"Node","value":{"next":{"ref":{"cell":1,"path":[]}},"val":2}},{"type":"Node","value":{"val":3,"next":{"ref":{"cell":0,"path":[]}}}}]}`

func TestSeededOracleRuns(t *testing.T) {
	if testing.Short() {
		t.Skip("execs go run")
	}
	for _, tc := range []struct {
		name, subject, args, seed string
		want                      []string
	}{
		{"seedRef result", "next", "ref:0", cycleSeed, []string{`"status":"ok"`, `"values":[{"cell":1,"path":[],"tag":"seedRef"}]`,
			`{"name":"next","value":{"cell":0,"path":[],"tag":"seedRef"}}`}},
		{"seedRef into an array field", "elem", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"Pair","value":{"a":[1,9,3],"b":true}}]}`,
			[]string{`"values":[{"cell":0,"path":["a",2],"tag":"seedRef"}]`}},
		{"cell pointing at an element", "inc", "ref:0.a[1]", `{"schema":"golean-seed-v1","cells":[{"type":"Pair","value":{"a":[1,9,3],"b":true}},{"type":"*int","value":{"ref":{"cell":0,"path":["a",1]}}}]}`,
			[]string{`"values":[{"kind":"int","tag":"int","value":10}]`, `{"cell":0,"path":["a",1],"tag":"seedRef"}`}},
		{"escaping result", "retLocal", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":41}]}`,
			[]string{`"status":"unsupported"`, `seed readout: result 0 holds a pointer outside the seed`}},
		{"escaping cell", "leak", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"*int","value":{"nil":true}}]}`,
			[]string{`"status":"unsupported"`, `seed readout: cell 0 holds a pointer outside the seed`}},
		{"zero-size pointee", "zp", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"Z","value":{}}]}`,
			[]string{`"status":"error"`, `pointer to the zero-size type main.Z`}},
		{"missing field", "val", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"Node","value":{"next":{"nil":true}}}]}`,
			[]string{`"status":"error"`, `seed: cell 0: struct main.Node: missing field val`}},
		{"unknown field", "val", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"Node","value":{"next":{"nil":true},"val":1,"nxt":2}}]}`,
			[]string{`seed: cell 0: struct main.Node: unknown field nxt`}},
		{"blank field", "useB", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"B","value":{"x":1}}]}`,
			[]string{`seed: cell 0: struct main.B: a blank field (_) cannot be seeded`}},
		{"int range", "inc", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":1},{"type":"int8","value":300}]}`,
			[]string{`seed: cell 1: int 300 out of range for int8`}},
		{"array length", "elem", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"Pair","value":{"a":[1,9],"b":true}}]}`,
			[]string{`seed: cell 0.a: expected array(3)`}},
		{"nil at non-pointer", "inc", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":{"nil":true}}]}`,
			[]string{`seed: cell 0: nil at non-pointer type int`}},
		{"ref type mismatch", "inc", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":1},{"type":"*int","value":{"ref":{"cell":2,"path":[]}}},{"type":"bool","value":true}]}`,
			[]string{`seed: cell 1: ref 2 has type *bool, *int expected`}},
		{"ref out of range", "inc", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":1},{"type":"*int","value":{"ref":{"cell":5,"path":[]}}}]}`,
			[]string{`ref to cell 5 out of range (2 cells)`}},
		{"path through a pointer", "inc", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":1},{"type":"*int","value":{"ref":{"cell":2,"path":["val"]}}},{"type":"*Node","value":{"nil":true}}]}`,
			[]string{`path .val on non-struct *main.Node`}},
		{"argument type mismatch", "inc", "ref:0", cycleSeed,
			[]string{`"status":"error"`, `seed: argument 1: ref:0: parameter has type *int; the reference points at main.Node`}},
		{"ref at a named pointer type", "viaNamed", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":5}]}`,
			[]string{`"status":"ok"`, `"values":[{"kind":"int","tag":"int","value":6}]`, `"seed":[{"kind":"int","tag":"int","value":6}]`}},
		{"nil at a named pointer type", "viaNamed", "nil", `{"schema":"golean-seed-v1","cells":[]}`,
			[]string{`"status":"ok"`, `"values":[{"kind":"int","tag":"int","value":-1}]`}},
		{"ref at an alias of a pointer type", "viaAlias", "ref:0", `{"schema":"golean-seed-v1","cells":[{"type":"int","value":5}]}`,
			[]string{`"status":"ok"`, `"values":[{"kind":"int","tag":"int","value":10}]`, `"seed":[{"kind":"int","tag":"int","value":10}]`}},
		{"nil at an alias of a pointer type", "viaAlias", "nil", `{"schema":"golean-seed-v1","cells":[]}`,
			[]string{`"status":"ok"`, `"values":[{"kind":"int","tag":"int","value":-2}]`}},
		{"nil at a non-pointer parameter", "take", "nil", cycleSeed,
			[]string{`"status":"error"`, `seed: argument 1: nil: parameter has type main.Node (kind struct) — a seed reference or nil only at a pointer parameter`}},
		{"ref at a non-pointer parameter", "take", "ref:0", cycleSeed,
			[]string{`"status":"error"`, `seed: argument 1: ref:0: parameter has type main.Node (kind struct) — a seed reference or nil only at a pointer parameter`}},
		{"ref at a named pointer type, wrong pointee", "viaNamed", "ref:0", cycleSeed,
			[]string{`"status":"error"`, `seed: argument 1: ref:0: parameter has type main.P; the reference points at main.Node`}},
	} {
		out, err := seededOracle(t, tc.subject, tc.args, tc.seed)
		if err != nil {
			t.Errorf("%s: generation refused: %v", tc.name, err)
			continue
		}
		for _, w := range tc.want {
			if !strings.Contains(out, w) {
				t.Errorf("%s: the seeded oracle's observation lacks %q: %s", tc.name, w, out)
			}
		}
	}
}

func TestSeededGenerationRefusals(t *testing.T) {
	for _, tc := range []struct{ name, subject, args, want string }{
		{"int at a pointer parameter", "inc", "5", "an integer cannot supply it"},
		{"arity", "inc", "ref:0,ref:0", "expects 1 argument(s), got 2"},
		{"bad token", "inc", "ref:0x", "malformed reference"},
	} {
		_, err := seededOracle(t, tc.subject, tc.args, cycleSeed)
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: generation = %v; want a refusal naming %q", tc.name, err, tc.want)
		}
	}
}
