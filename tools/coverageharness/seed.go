package main

// The SEEDED mode of the oracle generator (seeded-heap slice C, 2026-10-12;
// design docs/2026-10-09_seeded-heap-design.md §7; [USER] Mike 2026-10-12
// «Agree on the two strategic questions, let's do it», relayed — GO, with the
// trusted-surface #2 change of this harness accepted).
//
// `--seed <file>` reads the SAME golean-seed-v1 file `golean native-json-run
// --seed` reads, and `--args` widens to the tokens `<int>` | `ref:k(.f|[i])*` |
// `nil`. The generated main allocates every cell (`new(T)`, the type spelling
// pasted verbatim — phase 1), fills them in cell order through reflect
// (phase 2: every cell exists before any is filled, so sharing and cycles are
// plain stores), binds the arguments, calls the subject, and encodes the
// observation in GoLean's seeded shape: a pointer into a seed cell is
// `{"tag":"seedRef","cell":k,"path":[…]}`, the `seed` key holds the cells'
// FINAL values, and a pointer outside the seed refuses the WHOLE observation
// with status `unsupported` (the text class of GoLean's «holds a pointer
// outside the seed»). The runtime half is seedRuntimeSource below.
//
// This file is the GENERATOR half: it validates the file's SHAPE and the
// type spellings before any source is written, refusing BY NAME exactly the
// classes GoLean's CLI decoder (GoLean/SeedFile.lean) refuses, so a seeded row
// never passes on one side's silence. The TYPING (ints at their kind, struct
// field sets, array lengths, ref target types, nil only at pointers) needs the
// program's types and is decided at run time by reflect over the very cells
// the program allocated (seedRuntimeSource) — the Go-side twin of the core
// resolver. Where the harness cannot mirror a GoLean acceptance exactly it
// refuses (fail closed: the row goes red, never green): a paired surrogate
// escape, a declared type GoLean resolves by D2's scan but Go cannot name
// from main (a function-local type: a compile error at go run).

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"strconv"
	"strings"
	"unicode/utf8"
)

const seedSchemaName = "golean-seed-v1"

// jv is a strictly-read JSON value: objects keep their keys in order and
// refuse duplicates at read time.
type jv struct {
	kind  byte // 'o' object, 'a' array, 'n' number, 's' string, 'b' bool, 'z' null
	keys  []string
	vals  map[string]*jv
	elems []*jv
	num   string
	str   string
	b     bool
}

// readStrictJSON reads one JSON value from raw with GoLean's byte discipline:
// valid UTF-8, no duplicate object keys, no fraction/exponent number tokens,
// nothing after the value. encoding/json replaces an unpaired surrogate
// escape by U+FFFD silently, so EVERY surrogate escape is refused here (a
// paired one GoLean accepts — the harness refuses it, fail closed).
func readStrictJSON(raw []byte) (*jv, error) {
	if !utf8.Valid(raw) {
		return nil, fmt.Errorf("JSON input is not valid UTF-8")
	}
	if i := surrogateEscape(raw); i >= 0 {
		return nil, fmt.Errorf("a \\u surrogate escape at byte %d: the harness's seed reader cannot carry it exactly (fail closed)", i)
	}
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.UseNumber()
	v, err := readValue(dec)
	if err != nil {
		return nil, fmt.Errorf("JSON parse error: %v", err)
	}
	if _, err := dec.Token(); err != io.EOF {
		return nil, fmt.Errorf("JSON parse error: trailing data after the top-level value")
	}
	return v, nil
}

// surrogateEscape: the offset of the first `\uD800`–`\uDFFF` escape inside a
// string, or -1.
func surrogateEscape(raw []byte) int {
	inStr, esc := false, false
	for i := 0; i < len(raw); i++ {
		c := raw[i]
		switch {
		case !inStr:
			if c == '"' {
				inStr = true
			}
		case esc:
			esc = false
			if c == 'u' && i+4 < len(raw) {
				if n, err := strconv.ParseUint(string(raw[i+1:i+5]), 16, 16); err == nil && n >= 0xD800 && n <= 0xDFFF {
					return i - 1
				}
			}
		case c == '\\':
			esc = true
		case c == '"':
			inStr = false
		}
	}
	return -1
}

func readValue(dec *json.Decoder) (*jv, error) {
	tok, err := dec.Token()
	if err != nil {
		return nil, err
	}
	return readFrom(dec, tok)
}

func readFrom(dec *json.Decoder, tok json.Token) (*jv, error) {
	switch t := tok.(type) {
	case json.Delim:
		switch t {
		case '{':
			o := &jv{kind: 'o', vals: map[string]*jv{}}
			for dec.More() {
				kt, err := dec.Token()
				if err != nil {
					return nil, err
				}
				k, ok := kt.(string)
				if !ok {
					return nil, fmt.Errorf("object key is not a string")
				}
				if _, dup := o.vals[k]; dup {
					return nil, fmt.Errorf("duplicate JSON object key %q", k)
				}
				v, err := readValue(dec)
				if err != nil {
					return nil, err
				}
				o.keys = append(o.keys, k)
				o.vals[k] = v
			}
			if _, err := dec.Token(); err != nil {
				return nil, err
			}
			return o, nil
		case '[':
			a := &jv{kind: 'a', elems: []*jv{}}
			for dec.More() {
				v, err := readValue(dec)
				if err != nil {
					return nil, err
				}
				a.elems = append(a.elems, v)
			}
			if _, err := dec.Token(); err != nil {
				return nil, err
			}
			return a, nil
		}
		return nil, fmt.Errorf("unexpected delimiter %v", t)
	case json.Number:
		if strings.ContainsAny(string(t), ".eE") {
			return nil, fmt.Errorf("number %s: a fraction or exponent is not allowed in %s (integers only)", t, seedSchemaName)
		}
		return &jv{kind: 'n', num: string(t)}, nil
	case string:
		return &jv{kind: 's', str: t}, nil
	case bool:
		return &jv{kind: 'b', b: t}, nil
	case nil:
		return &jv{kind: 'z'}, nil
	}
	return nil, fmt.Errorf("unexpected JSON token %v", tok)
}

func exactKeys(where string, o *jv, want ...string) error {
	if o.kind != 'o' {
		return fmt.Errorf("%s: expected an object", where)
	}
	if len(o.keys) == len(want) {
		ok := true
		for _, w := range want {
			if _, has := o.vals[w]; !has {
				ok = false
			}
		}
		if ok {
			return nil
		}
	}
	return fmt.Errorf("%s: expected exactly keys %v, got %v", where, want, o.keys)
}

// seedCellSpec is one validated cell: its type spelling (pasted verbatim
// into `new(T)`) — the value is re-read at run time from the embedded file.
type seedCellSpec struct {
	typ string
}

// parseSeedFile validates a golean-seed-v1 file's bytes: the envelope, every
// type spelling, every value's shape. The refusal names the position.
func parseSeedFile(raw []byte) ([]seedCellSpec, error) {
	root, err := readStrictJSON(raw)
	if err != nil {
		return nil, err
	}
	if err := exactKeys("seed", root, "schema", "cells"); err != nil {
		return nil, err
	}
	if s := root.vals["schema"]; s.kind != 's' || s.str != seedSchemaName {
		return nil, fmt.Errorf("seed.schema: expected %q", seedSchemaName)
	}
	cells := root.vals["cells"]
	if cells.kind != 'a' {
		return nil, fmt.Errorf("seed.cells: expected an array")
	}
	out := []seedCellSpec{}
	for k, c := range cells.elems {
		where := fmt.Sprintf("seed.cells[%d]", k)
		if err := exactKeys(where, c, "type", "value"); err != nil {
			return nil, err
		}
		t := c.vals["type"]
		if t.kind != 's' {
			return nil, fmt.Errorf("%s.type: expected a type spelling (string)", where)
		}
		if err := checkTypeSpelling(t.str, t.str); err != nil {
			return nil, fmt.Errorf("%s.type: %v", where, err)
		}
		if err := checkSeedValue(where+".value", c.vals["value"]); err != nil {
			return nil, err
		}
		out = append(out, seedCellSpec{typ: t.str})
	}
	return out, nil
}

// refNilLimit: GoLean's stated v1 limit (SeedFile.refNilLimit), the same text.
const refNilLimit = "a struct with a field named ref or nil is not expressible in golean-seed-v1"

// checkSeedValue: the §1 SeedJson shape.
func checkSeedValue(where string, v *jv) error {
	switch v.kind {
	case 'n':
		if !isDecimalInt(v.num) {
			return fmt.Errorf("%s: not an integer", where)
		}
		return nil
	case 'b':
		return nil
	case 'z':
		return fmt.Errorf("%s: null is not a seed value (a nil pointer is {\"nil\":true})", where)
	case 's':
		return fmt.Errorf("%s: a string is not a seed value in golean-seed-v1", where)
	case 'a':
		for i, e := range v.elems {
			if err := checkSeedValue(fmt.Sprintf("%s[%d]", where, i), e); err != nil {
				return err
			}
		}
		return nil
	}
	_, hasRef := v.vals["ref"]
	_, hasNil := v.vals["nil"]
	if hasRef || hasNil {
		if len(v.keys) != 1 {
			return fmt.Errorf("%s: an object with a `ref` or `nil` key is the reference / nil form and carries nothing else (got keys %v) — %s", where, v.keys, refNilLimit)
		}
		if hasNil {
			if n := v.vals["nil"]; n.kind != 'b' || !n.b {
				return fmt.Errorf("%s.nil: expected true (a nil pointer is {\"nil\":true}) — %s", where, refNilLimit)
			}
			return nil
		}
		return checkRefBody(where+".ref", v.vals["ref"])
	}
	for _, k := range v.keys {
		if err := checkSeedValue(where+"."+k, v.vals[k]); err != nil {
			return err
		}
	}
	return nil
}

func checkRefBody(where string, v *jv) error {
	if v.kind != 'o' {
		return fmt.Errorf("%s: expected {\"cell\":<nat>,\"path\":[…]} — %s", where, refNilLimit)
	}
	if err := exactKeys(where, v, "cell", "path"); err != nil {
		return err
	}
	if c := v.vals["cell"]; c.kind != 'n' || !isDecimalNat(c.num) {
		return fmt.Errorf("%s.cell: expected a nat (the cell's index in the seed)", where)
	}
	p := v.vals["path"]
	if p.kind != 'a' {
		return fmt.Errorf("%s.path: expected an array", where)
	}
	for i, e := range p.elems {
		switch {
		case e.kind == 's':
		case e.kind == 'n' && isDecimalNat(e.num):
		default:
			return fmt.Errorf("%s.path[%d]: a path element is a field name (string) or an index (nat)", where, i)
		}
	}
	return nil
}

// isDecimalInt / isDecimalNat: the JSON integer token GoLean's decoder takes
// (sign only for ints; the JSON grammar already forbids leading zeros).
func isDecimalInt(s string) bool {
	return isDecimalNat(strings.TrimPrefix(s, "-"))
}

func isDecimalNat(s string) bool {
	if s == "" {
		return false
	}
	for _, c := range s {
		if c < '0' || c > '9' {
			return false
		}
	}
	return true
}

// The type-spelling grammar (§1; GoLean/SeedFile.lean parseTypeSpelling):
// `*T`, `[n]T`, an ASCII identifier. The harness has no type table: an
// <Ident> is pasted and the Go compiler resolves it (undeclared → a loud
// compile error at go run). Everything GoLean refuses BY CLASS is refused
// here by the same class.
var v1Builtins = map[string]bool{"bool": true, "int": true, "uint": true, "int8": true, "uint8": true,
	"int16": true, "uint16": true, "int32": true, "uint32": true, "int64": true, "uint64": true}

var outsideBuiltins = map[string]string{
	"uintptr": "uintptr", "float32": "a float type (float32)", "float64": "a float type (float64)",
	"complex64": "a complex type (complex64)", "complex128": "a complex type (complex128)",
	"string": "string", "byte": "byte (spell it uint8)", "rune": "rune (spell it int32)",
	"any": "an interface type (any)", "error": "an interface type (error)",
}

var typeKeywords = map[string]string{"chan": "a channel type", "func": "a function type",
	"interface": "an interface type", "struct": "an anonymous struct type", "map": "a map type"}

func notInV1(outer, what string) error {
	return fmt.Errorf("type spelling %s: %s is not in golean-seed-v1", outer, what)
}

func isASCIIIdent(s string) bool {
	if s == "" || s == "_" {
		return false
	}
	for i, c := range s {
		letter := c == '_' || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
		if !letter && (i == 0 || c < '0' || c > '9') {
			return false
		}
	}
	return true
}

func checkTypeSpelling(outer, s string) error {
	switch {
	case strings.HasPrefix(s, "*"):
		return checkTypeSpelling(outer, s[1:])
	case strings.HasPrefix(s, "[]"):
		return notInV1(outer, "a slice type")
	case strings.HasPrefix(s, "["):
		end := strings.Index(s, "]")
		if end < 0 {
			return fmt.Errorf("type spelling %s: unterminated array length", outer)
		}
		n := s[1:end]
		if !isDecimalNat(n) || (len(n) > 1 && n[0] == '0') {
			return fmt.Errorf("type spelling %s: array length %s is not a decimal nat (no sign, no leading zeros, no constant expression)", outer, n)
		}
		return checkTypeSpelling(outer, s[end+1:])
	case isASCIIIdent(s):
		if what, ok := typeKeywords[s]; ok {
			return notInV1(outer, what)
		}
		if what, ok := outsideBuiltins[s]; ok {
			return notInV1(outer, what)
		}
		if strings.HasPrefix(s, "_golean") {
			return fmt.Errorf("type spelling %s: the _golean prefix is reserved for the harness", outer)
		}
		return nil // a v1 builtin, or an <Ident> the compiler resolves
	}
	for _, lit := range []struct{ prefix, what string }{
		{"map[", "a map type"}, {"chan ", "a channel type"}, {"chan<-", "a channel type"}, {"<-chan", "a channel type"},
		{"func(", "a function type"}, {"func (", "a function type"}, {"interface{", "an interface type"},
		{"interface {", "an interface type"}, {"struct{", "an anonymous struct type"}, {"struct {", "an anonymous struct type"},
		{"sync.", "a sync type"},
	} {
		if strings.HasPrefix(s, lit.prefix) {
			return notInV1(outer, lit.what)
		}
	}
	if parts := strings.Split(s, "."); len(parts) > 1 {
		all := true
		for _, p := range parts {
			all = all && isASCIIIdent(p)
		}
		if all {
			return notInV1(outer, "a package-qualified type (write the declared type's unqualified Go name)")
		}
	}
	return fmt.Errorf("type spelling %s: not in the golean-seed-v1 type grammar (bool | int | int8 | … | uint64 | [<nat>]T | *T | <Ident>)", outer)
}

// seedArg is one seeded-mode argument token.
type seedArg struct {
	kind  byte   // 'i' integer literal, 'r' seed reference, 'n' nil
	lit   string // the integer literal ('i')
	cell  int    // the referenced cell ('r')
	path  []any  // field names (string) and indices (int), root-first ('r')
	token string // the token as written
}

// parseSeedArgs reads the seeded `--args` column: `-` or comma-separated
// `<int>` | `ref:k(.f|[i])*` | `nil` (the native-json-run flags --arg-int /
// --arg-ref / --arg-nil; the --arg-ref grammar of GoLean/SeedFile.lean
// parseArgRef: decimal nats without leading zeros, ASCII identifiers).
func parseSeedArgs(raw string) ([]seedArg, error) {
	if raw == "-" {
		return nil, nil
	}
	out := []seedArg{}
	for _, tok := range strings.Split(raw, ",") {
		switch {
		case tok == "nil":
			out = append(out, seedArg{kind: 'n', token: tok})
		case strings.HasPrefix(tok, "ref:"):
			cell, path, err := parseRefSpec(tok[len("ref:"):])
			if err != nil {
				return nil, fmt.Errorf("argument %q: %v", tok, err)
			}
			out = append(out, seedArg{kind: 'r', cell: cell, path: path, token: tok})
		default:
			if _, err := parseArgs(tok); err != nil {
				return nil, fmt.Errorf("argument %q is not an integer, ref:k(.f|[i])* or nil: %v", tok, err)
			}
			out = append(out, seedArg{kind: 'i', lit: tok, token: tok})
		}
	}
	return out, nil
}

func parseNat(s string) (int, bool) {
	if !isDecimalNat(s) || (len(s) > 1 && s[0] == '0') {
		return 0, false
	}
	n, err := strconv.Atoi(s)
	return n, err == nil
}

func parseRefSpec(spec string) (int, []any, error) {
	bad := fmt.Errorf("malformed reference %s (expected k(.field|[i])*, e.g. 0, 0.next, 1[2], 0.a[3].b)", spec)
	i := 0
	for i < len(spec) && spec[i] >= '0' && spec[i] <= '9' {
		i++
	}
	cell, ok := parseNat(spec[:i])
	if !ok {
		return 0, nil, bad
	}
	path := []any{}
	for i < len(spec) {
		switch spec[i] {
		case '.':
			j := i + 1
			for j < len(spec) && (spec[j] == '_' || ('a' <= spec[j] && spec[j] <= 'z') || ('A' <= spec[j] && spec[j] <= 'Z') || ('0' <= spec[j] && spec[j] <= '9')) {
				j++
			}
			if !isASCIIIdent(spec[i+1 : j]) {
				return 0, nil, bad
			}
			path = append(path, spec[i+1:j])
			i = j
		case '[':
			j := strings.IndexByte(spec[i:], ']')
			if j < 0 {
				return 0, nil, bad
			}
			n, ok := parseNat(spec[i+1 : i+j])
			if !ok {
				return 0, nil, bad
			}
			path = append(path, n)
			i += j + 1
		default:
			return 0, nil, bad
		}
	}
	return cell, path, nil
}

// goPathLiteral renders a path as the Go literal `[]any{"next", 0}`.
func goPathLiteral(path []any) string {
	parts := make([]string, len(path))
	for i, e := range path {
		switch e := e.(type) {
		case string:
			parts[i] = strconv.Quote(e)
		case int:
			parts[i] = strconv.Itoa(e)
		}
	}
	return "[]any{" + strings.Join(parts, ", ") + "}"
}

// seededMain: the body of the seeded harness's main() after the crash hook —
// phase 1 (allocate every cell), phase 2 (fill), the arguments, the call, the
// observation with its `seed` key.
func seededMain(subject string, paramTypes []string, variadic bool, resultCount int, cells []seedCellSpec, args []seedArg, expectedStatus string) (string, error) {
	if variadic {
		return "", fmt.Errorf("seeded mode: variadic subject %s is not supported in golean-seed-v1 (fail closed)", subject)
	}
	if len(args) != len(paramTypes) {
		return "", fmt.Errorf("subject %s expects %d argument(s), got %d", subject, len(paramTypes), len(args))
	}
	if expectedStatus == "ok" && resultCount == 0 && len(cells) == 0 {
		return "", fmt.Errorf("ok subject %s must return at least one observable value (or seed a cell)", subject)
	}
	var b strings.Builder
	cellNames := make([]string, len(cells))
	for k, c := range cells {
		cellNames[k] = fmt.Sprintf("_golean_c%d", k)
		fmt.Fprintf(&b, "\t%s := new(%s)\n", cellNames[k], c.typ)
	}
	fmt.Fprintf(&b, "\t_goleanSeedCells = []any{%s}\n", strings.Join(cellNames, ", "))
	fmt.Fprintf(&b, "\tif _goleanErr := _goleanSeedBuild(); _goleanErr != nil {\n\t\t_goleanPrintError(_goleanErr.Error())\n\t\treturn\n\t}\n")
	argExprs := make([]string, len(args))
	for i, a := range args {
		pt := paramTypes[i]
		pointer := strings.HasPrefix(pt, "*")
		name := fmt.Sprintf("_golean_a%d", i)
		argExprs[i] = name
		switch a.kind {
		case 'i':
			if pointer {
				return "", fmt.Errorf("argument %d (%s): parameter has pointer type %s — an integer cannot supply it", i+1, a.token, pt)
			}
			argExprs[i] = fmt.Sprintf("%s(%s)", pt, a.lit)
		case 'n':
			if !pointer {
				return "", fmt.Errorf("argument %d (nil): parameter has type %s — nil only at a pointer parameter (*T) in golean-seed-v1", i+1, pt)
			}
			fmt.Fprintf(&b, "\tvar %s %s = nil\n", name, pt)
		case 'r':
			if !pointer {
				return "", fmt.Errorf("argument %d (%s): parameter has type %s — a seed reference only at a pointer parameter (*T)", i+1, a.token, pt)
			}
			fmt.Fprintf(&b, "\tvar %s %s\n", name, pt)
			fmt.Fprintf(&b, "\t{\n\t\t_goleanRef, _goleanErr := _goleanSeedRef(%d, %s, %q)\n", a.cell, goPathLiteral(a.path), fmt.Sprintf("argument %d: %s", i+1, a.token))
			fmt.Fprintf(&b, "\t\tif _goleanErr != nil {\n\t\t\t_goleanPrintError(_goleanErr.Error())\n\t\t\treturn\n\t\t}\n")
			fmt.Fprintf(&b, "\t\t_goleanP, _goleanOk := _goleanRef.(%s)\n", pt)
			fmt.Fprintf(&b, "\t\tif !_goleanOk {\n\t\t\t_goleanPrintError(_golean_fmt.Sprintf(%q, _goleanRef))\n\t\t\treturn\n\t\t}\n",
				fmt.Sprintf("seed: argument %d: parameter has type %s; %s points at %%T", i+1, pt, a.token))
			fmt.Fprintf(&b, "\t\t%s = _goleanP\n\t}\n", name)
		}
	}
	names := make([]string, resultCount)
	for i := range names {
		names[i] = fmt.Sprintf("_golean_r%d", i)
	}
	if resultCount == 0 {
		fmt.Fprintf(&b, "\t%s(%s)\n", subject, strings.Join(argExprs, ", "))
	} else {
		fmt.Fprintf(&b, "\t%s := %s(%s)\n", strings.Join(names, ", "), subject, strings.Join(argExprs, ", "))
	}
	fmt.Fprintf(&b, "\t_goleanValues := []any{}\n")
	for i, name := range names {
		fmt.Fprintf(&b, "\t{\n\t\t_goleanSeedWhat = %q\n", fmt.Sprintf("result %d", i))
		fmt.Fprintf(&b, "\t\t_goleanValue, _goleanErr := _goleanObservationValue(&%s)\n", name)
		fmt.Fprintf(&b, "\t\tif _goleanErr != nil {\n\t\t\t_goleanPrintSeedError(_goleanErr)\n\t\t\treturn\n\t\t}\n")
		fmt.Fprintf(&b, "\t\t_goleanValues = append(_goleanValues, _goleanValue)\n\t}\n")
	}
	fmt.Fprintf(&b, "\t_goleanSeedObs, _goleanErr := _goleanSeedFinal()\n")
	fmt.Fprintf(&b, "\tif _goleanErr != nil {\n\t\t_goleanPrintSeedError(_goleanErr)\n\t\treturn\n\t}\n")
	fmt.Fprintf(&b, "\t_goleanPrintOkSeed(_goleanValues, _goleanSeedObs)\n")
	return b.String(), nil
}

// The seeded harness's extra imports (inserted into the shared import block).
const seedImports = "\t_golean_strconv \"strconv\"\n\t_golean_strings \"strings\"\n\t_golean_unsafe \"unsafe\"\n"

// The seeded encoder's pointer arm (inserted before `default:` in the shared
// _goleanReflectValue; the unseeded harness has none and refuses pointers).
const seedPointerArm = "\tcase _golean_reflect.Pointer:\n\t\treturn _goleanSeedPointer(value)\n"

// seedRuntimeDecls: the runtime half, with the file's bytes embedded as a Go
// string literal (validated above; re-read at run time with UseNumber).
func seedRuntimeDecls(raw []byte) string {
	return "\nconst _goleanSeedJSON = " + strconv.Quote(string(raw)) + "\n" + seedRuntimeSource
}

// seedRuntimeSource is the Go-side resolver and the seed-aware observation
// helpers. HOW A POINTER IS MADE SEED-RELATIVE, and why it is exact: a
// pointer is matched by (address, element type) against every addressable
// sub-object of every cell — the cell roots, their struct fields and array
// elements, recursively — read from the live cells at observation time
// (the cells are heap objects: Go's collector does not move heap objects).
// For a NON-zero-size element type the match is unique: two distinct
// sub-objects at one address overlap, so one contains the other; with equal
// types they have equal sizes, so the containment is at offset 0 with
// nothing else beside it — a type containing itself by value, which Go
// forbids. A non-seed object cannot share the address either (live objects
// of non-zero size do not overlap). So «found» is exactly «this cell, this
// path» and «not found» is exactly «outside the seed». A ZERO-size element
// type has no such guarantee (gc may place zero-size objects at one shared
// address) and refuses by name. Paths read field names as declared
// (reflect StructField.Name) and indices as ints: the machine's
// seedRelative? path (field names, indices) over the same declared types.
const seedRuntimeSource = `
var _goleanSeedCells []any

// _goleanSeedWhat names the observed position for the escape refusal
// ("result i" / "cell k"), as GoLean's seededObs does.
var _goleanSeedWhat string

// _goleanSeedEscape: a pointer outside the seed — status unsupported, the
// text class of GoLean's seed readout refusal.
type _goleanSeedEscape struct{ msg string }

func (e *_goleanSeedEscape) Error() string { return e.msg }

func _goleanPrintSeedError(err error) {
	status := "error"
	if _, ok := err.(*_goleanSeedEscape); ok {
		status = "unsupported"
	}
	if e := _golean_json.NewEncoder(_golean_os.Stdout).Encode(map[string]any{"schema": "golean-observation-v1", "status": status, "message": err.Error()}); e != nil {
		panic(e)
	}
}

func _goleanPrintOkSeed(values []any, seed []any) {
	if err := _golean_json.NewEncoder(_golean_os.Stdout).Encode(map[string]any{"schema": "golean-observation-v1", "status": "ok", "values": values, "seed": seed}); err != nil {
		panic(err)
	}
}

// _goleanSeedSettable: a settable view of an addressable value, also through
// unexported fields (the cells' fields are the program's own; this is the
// assignment the Go prologue would write, done by reflect).
func _goleanSeedSettable(v _golean_reflect.Value) _golean_reflect.Value {
	return _golean_reflect.NewAt(v.Type(), _golean_unsafe.Pointer(v.UnsafeAddr())).Elem()
}

func _goleanSeedRender(cell int, path []any) string {
	var b _golean_strings.Builder
	_golean_fmt.Fprintf(&b, "%d", cell)
	for _, e := range path {
		switch e := e.(type) {
		case string:
			b.WriteString("." + e)
		case int:
			_golean_fmt.Fprintf(&b, "[%d]", e)
		}
	}
	return b.String()
}

// _goleanSeedTarget walks cell j's DECLARED type along path (no pointer is
// followed — the core's seedPathTy): a field needs a struct, an index an
// array with the index in range.
func _goleanSeedTarget(where string, j int, path []any) (_golean_reflect.Value, error) {
	if j < 0 || j >= len(_goleanSeedCells) {
		return _golean_reflect.Value{}, _golean_fmt.Errorf("seed: %s: ref to cell %d out of range (%d cells)", where, j, len(_goleanSeedCells))
	}
	v := _golean_reflect.ValueOf(_goleanSeedCells[j]).Elem()
	for _, e := range path {
		switch e := e.(type) {
		case string:
			if v.Kind() != _golean_reflect.Struct {
				return _golean_reflect.Value{}, _golean_fmt.Errorf("seed: %s: path .%s on non-struct %s", where, e, v.Type())
			}
			idx := -1
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).Name == e {
					idx = i
				}
			}
			if idx < 0 {
				return _golean_reflect.Value{}, _golean_fmt.Errorf("seed: %s: unknown field %s of %s", where, e, v.Type())
			}
			v = v.Field(idx)
		case int:
			if v.Kind() != _golean_reflect.Array || e < 0 || e >= v.Len() {
				return _golean_reflect.Value{}, _golean_fmt.Errorf("seed: %s: index %d out of range for %s", where, e, v.Type())
			}
			v = v.Index(e)
		default:
			return _golean_reflect.Value{}, _golean_fmt.Errorf("seed: %s: internal: path element %v", where, e)
		}
	}
	return v, nil
}

// _goleanSeedRef: a pointer (as any, *T dynamic type) to cell j's sub-object.
func _goleanSeedRef(j int, path []any, where string) (any, error) {
	t, err := _goleanSeedTarget(where, j, path)
	if err != nil {
		return nil, err
	}
	return _golean_reflect.NewAt(t.Type(), _golean_unsafe.Pointer(t.UnsafeAddr())).Interface(), nil
}

func _goleanSeedPathOf(raw []any) ([]any, bool) {
	out := []any{}
	for _, e := range raw {
		switch e := e.(type) {
		case string:
			out = append(out, e)
		case _golean_json.Number:
			n, err := _golean_strconv.Atoi(string(e))
			if err != nil || n < 0 {
				return nil, false
			}
			out = append(out, n)
		default:
			return nil, false
		}
	}
	return out, true
}

// _goleanSeedFill stores the seed value val into the addressable dst at its
// DECLARED type — the Go-side twin of the core resolver's typing: ints
// range-checked at their kind (never wrapped), every declared struct field
// REQUIRED and no other (no zero-fill), a blank field refused, arrays of the
// exact length, nil only at a pointer, a ref's target type equal to the
// pointer's element type, any other kind refused as not in golean-seed-v1.
func _goleanSeedFill(where string, dst _golean_reflect.Value, val any) error {
	t := dst.Type()
	obj, isObj := val.(map[string]any)
	if isObj {
		if _, ok := obj["nil"]; ok {
			if dst.Kind() != _golean_reflect.Pointer {
				return _golean_fmt.Errorf("seed: %s: nil at non-pointer type %s", where, t)
			}
			_goleanSeedSettable(dst).Set(_golean_reflect.Zero(t))
			return nil
		}
		if r, ok := obj["ref"]; ok {
			body := r.(map[string]any)
			j, err := _golean_strconv.Atoi(string(body["cell"].(_golean_json.Number)))
			if err != nil {
				return _golean_fmt.Errorf("seed: %s: ref cell %v", where, body["cell"])
			}
			path, ok := _goleanSeedPathOf(body["path"].([]any))
			if !ok {
				return _golean_fmt.Errorf("seed: %s: ref path %v", where, body["path"])
			}
			if dst.Kind() != _golean_reflect.Pointer {
				return _golean_fmt.Errorf("seed: %s: ref %s at non-pointer type %s", where, _goleanSeedRender(j, path), t)
			}
			target, err := _goleanSeedTarget(where, j, path)
			if err != nil {
				return err
			}
			if target.Type() != t.Elem() {
				return _golean_fmt.Errorf("seed: %s: ref %s has type *%s, %s expected", where, _goleanSeedRender(j, path), target.Type(), t)
			}
			_goleanSeedSettable(dst).Set(_golean_reflect.NewAt(target.Type(), _golean_unsafe.Pointer(target.UnsafeAddr())))
			return nil
		}
	}
	switch dst.Kind() {
	case _golean_reflect.Bool:
		b, ok := val.(bool)
		if !ok {
			return _golean_fmt.Errorf("seed: %s: expected a bool at %s, got %v", where, t, val)
		}
		_goleanSeedSettable(dst).SetBool(b)
		return nil
	case _golean_reflect.Int, _golean_reflect.Int8, _golean_reflect.Int16, _golean_reflect.Int32, _golean_reflect.Int64:
		n, ok := val.(_golean_json.Number)
		if !ok {
			return _golean_fmt.Errorf("seed: %s: expected an int at %s, got %v", where, t, val)
		}
		i, err := _golean_strconv.ParseInt(string(n), 10, 64)
		if err != nil || dst.OverflowInt(i) {
			return _golean_fmt.Errorf("seed: %s: int %s out of range for %s", where, n, dst.Kind())
		}
		_goleanSeedSettable(dst).SetInt(i)
		return nil
	case _golean_reflect.Uint, _golean_reflect.Uint8, _golean_reflect.Uint16, _golean_reflect.Uint32, _golean_reflect.Uint64:
		n, ok := val.(_golean_json.Number)
		if !ok {
			return _golean_fmt.Errorf("seed: %s: expected an int at %s, got %v", where, t, val)
		}
		u, err := _golean_strconv.ParseUint(string(n), 10, 64)
		if err != nil || dst.OverflowUint(u) {
			return _golean_fmt.Errorf("seed: %s: int %s out of range for %s", where, n, dst.Kind())
		}
		_goleanSeedSettable(dst).SetUint(u)
		return nil
	case _golean_reflect.Array:
		xs, ok := val.([]any)
		if !ok || len(xs) != dst.Len() {
			return _golean_fmt.Errorf("seed: %s: expected array(%d) at %s, got %v", where, dst.Len(), t, val)
		}
		for i, x := range xs {
			if err := _goleanSeedFill(_golean_fmt.Sprintf("%s[%d]", where, i), dst.Index(i), x); err != nil {
				return err
			}
		}
		return nil
	case _golean_reflect.Struct:
		if !isObj {
			return _golean_fmt.Errorf("seed: %s: expected a struct value at %s, got %v", where, t, val)
		}
		for i := 0; i < t.NumField(); i++ {
			name := t.Field(i).Name
			if name == "_" {
				return _golean_fmt.Errorf("seed: %s: struct %s: a blank field (_) cannot be seeded", where, t)
			}
			x, ok := obj[name]
			if !ok {
				return _golean_fmt.Errorf("seed: %s: struct %s: missing field %s", where, t, name)
			}
			if err := _goleanSeedFill(where+"."+name, dst.Field(i), x); err != nil {
				return err
			}
		}
		for k := range obj {
			declared := false
			for i := 0; i < t.NumField(); i++ {
				declared = declared || t.Field(i).Name == k
			}
			if !declared {
				return _golean_fmt.Errorf("seed: %s: struct %s: unknown field %s", where, t, k)
			}
		}
		return nil
	}
	return _golean_fmt.Errorf("seed: %s: value at type %s not in golean-seed-v1", where, t)
}

// _goleanSeedBuild: phase 2 — fill every (already allocated) cell in order.
func _goleanSeedBuild() error {
	dec := _golean_json.NewDecoder(_golean_strings.NewReader(_goleanSeedJSON))
	dec.UseNumber()
	var root map[string]any
	if err := dec.Decode(&root); err != nil {
		return _golean_fmt.Errorf("seed: internal: re-reading the validated seed file: %v", err)
	}
	cells, _ := root["cells"].([]any)
	if len(cells) != len(_goleanSeedCells) {
		return _golean_fmt.Errorf("seed: internal: %d cells in the file, %d allocated", len(cells), len(_goleanSeedCells))
	}
	for k, c := range cells {
		where := _golean_fmt.Sprintf("cell %d", k)
		if err := _goleanSeedFill(where, _golean_reflect.ValueOf(_goleanSeedCells[k]).Elem(), c.(map[string]any)["value"]); err != nil {
			return err
		}
	}
	return nil
}

// _goleanSeedLocate: the path of the sub-object of v (cell-rooted, path so
// far) at address p with type t, if any.
func _goleanSeedLocate(v _golean_reflect.Value, p _golean_unsafe.Pointer, t _golean_reflect.Type, path []any) ([]any, bool) {
	if v.Type() == t && _golean_unsafe.Pointer(v.UnsafeAddr()) == p {
		return path, true
	}
	switch v.Kind() {
	case _golean_reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			sub := append(append([]any{}, path...), v.Type().Field(i).Name)
			if r, ok := _goleanSeedLocate(v.Field(i), p, t, sub); ok {
				return r, true
			}
		}
	case _golean_reflect.Array:
		for i := 0; i < v.Len(); i++ {
			sub := append(append([]any{}, path...), i)
			if r, ok := _goleanSeedLocate(v.Index(i), p, t, sub); ok {
				return r, true
			}
		}
	}
	return nil, false
}

// _goleanSeedPointer: a pointer observed seed-relative, or the refusal.
func _goleanSeedPointer(value _golean_reflect.Value) (any, error) {
	if value.IsNil() {
		return map[string]any{"tag": "nil"}, nil
	}
	elem := value.Type().Elem()
	if elem.Size() == 0 {
		return nil, _golean_fmt.Errorf("seed readout: %s holds a pointer to the zero-size type %s — its address does not identify a seed position; not observable in golean-seed-v1", _goleanSeedWhat, elem)
	}
	p := value.UnsafePointer()
	for k, c := range _goleanSeedCells {
		if path, ok := _goleanSeedLocate(_golean_reflect.ValueOf(c).Elem(), p, elem, []any{}); ok {
			return map[string]any{"tag": "seedRef", "cell": k, "path": path}, nil
		}
	}
	return nil, &_goleanSeedEscape{_golean_fmt.Sprintf("seed readout: %s holds a pointer outside the seed (a parameter, result, global or run-allocated object) — not expressible seed-relative", _goleanSeedWhat)}
}

// _goleanSeedFinal: the cells' FINAL values, in cell order.
func _goleanSeedFinal() ([]any, error) {
	out := []any{}
	for k, c := range _goleanSeedCells {
		_goleanSeedWhat = _golean_fmt.Sprintf("cell %d", k)
		v, err := _goleanReflectValue(_golean_reflect.ValueOf(c).Elem())
		if err != nil {
			return nil, err
		}
		out = append(out, v)
	}
	return out, nil
}
`
