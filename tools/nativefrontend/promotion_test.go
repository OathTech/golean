package main

// Promotion records (G-P S1; design note
// docs/2026-09-28_gp-method-promotion-design.md §4/§5; G-P PASSED [USER]
// 2026-09-28, relayed): the emitter writes one `promotions` record per
// promoted method-set entry — beside the synthesized wrapper or the
// declaration-only stub it emits today — from the same go/types selection.
// These tests pin the record shapes for every embedding form the design
// distinguishes (value embed, pointer embed, multi-hop, an embedded
// interface field, a *T-only entry, the sync-primitive stub, an FR-23
// signature stub, a generic instantiation) and the one-to-one pairing
// with the wrappers/stubs the decoder cross-checks.

import (
	"encoding/json"
	"reflect"
	"sort"
	"strings"
	"testing"
)

// promotionRecords indexes the wire's records by "<carrier>.<member name>".
func promotionRecords(t *testing.T, program map[string]any) map[string]map[string]any {
	t.Helper()
	raw, ok := program["promotions"].([]any)
	if !ok {
		t.Fatalf("no promotions array on the wire (%T)", program["promotions"])
	}
	out := map[string]map[string]any{}
	for _, r := range raw {
		m := r.(map[string]any)
		key := m["type"].(string) + "." + m["member"].(memberID).Name
		if _, dup := out[key]; dup {
			t.Fatalf("duplicate promotion record %s", key)
		}
		out[key] = m
	}
	return out
}

// wrapperCallee returns the FuncId a synthesized wrapper's body forwards to.
func wrapperCallee(t *testing.T, w map[string]any) string {
	t.Helper()
	first := w["body"].(map[string]any)["body"].([]any)[0].(map[string]any)
	var call map[string]any
	if first["stmt"] == "expr" {
		call = first["expr"].(map[string]any)
	} else {
		call = first["rhs"].([]any)[0].(map[string]any)
	}
	return call["func"].(string)
}

func expectRecord(t *testing.T, recs map[string]map[string]any, key string, inPtrSetOnly bool, path []map[string]any, adjust string, target map[string]any) map[string]any {
	t.Helper()
	r, ok := recs[key]
	if !ok {
		t.Fatalf("no promotion record %s (have %v)", key, recordKeys(recs))
	}
	if r["inPtrSetOnly"] != inPtrSetOnly {
		t.Errorf("%s: inPtrSetOnly = %v, want %v", key, r["inPtrSetOnly"], inPtrSetOnly)
	}
	if r["adjust"] != adjust {
		t.Errorf("%s: adjust = %v, want %v", key, r["adjust"], adjust)
	}
	gotPath := []map[string]any{}
	for _, h := range r["path"].([]any) {
		gotPath = append(gotPath, h.(map[string]any))
	}
	if !reflect.DeepEqual(gotPath, path) {
		t.Errorf("%s: path = %s, want %s", key, fmtJSON(gotPath), fmtJSON(path))
	}
	if !reflect.DeepEqual(r["target"], target) {
		t.Errorf("%s: target = %s, want %s", key, fmtJSON(r["target"]), fmtJSON(target))
	}
	return r
}

func recordKeys(m map[string]map[string]any) []string {
	out := []string{}
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

func hop(owner, field string, ptr bool) map[string]any {
	return map[string]any{"owner": owner, "field": field, "ptr": ptr}
}

func methodTarget(recv, name, pkg string) map[string]any {
	return map[string]any{"method": methodFuncKey(recv, memberID{Name: name, Package: pkg})}
}

// checkPairing — every wrapper and every promoted stub has exactly one
// record with the same carrier and member, the record's set membership
// matches the wrapper's receiver kind, a wrapper's callee is the record's
// target, and a stub's cause/signature are the record's. The count of
// records equals wrappers + promoted stubs.
func checkPairing(t *testing.T, program map[string]any, recs map[string]map[string]any) {
	t.Helper()
	paired := 0
	for _, m := range program["methods"].([]any) {
		mm := m.(map[string]any)
		isWrapper := mm["wrapper"] == true
		reason, _ := mm["unsupported"].(string)
		isPromotedStub := strings.HasPrefix(reason, "promoted ")
		if !isWrapper && !isPromotedStub {
			continue
		}
		paired++
		key := mm["recvType"].(string) + "." + mm["id"].(memberID).Name
		r, ok := recs[key]
		if !ok {
			t.Errorf("wrapper/stub %s has no promotion record", key)
			continue
		}
		recvIsPtr := mm["recv"].(map[string]any)["type"].(map[string]any)["kind"] == "pointer"
		if r["inPtrSetOnly"] != recvIsPtr {
			t.Errorf("%s: record inPtrSetOnly=%v but the wrapper/stub receiver pointer=%v", key, r["inPtrSetOnly"], recvIsPtr)
		}
		if isWrapper {
			if _, stub := r["unsupported"]; stub {
				t.Errorf("%s: a wrapper's record carries unsupported", key)
			}
			callee := wrapperCallee(t, mm)
			tgt := r["target"].(map[string]any)
			want, isMethod := tgt["method"].(string)
			if !isMethod {
				want = methodFuncKey(tgt["iface"].(string), mm["id"].(memberID))
			}
			if callee != want {
				t.Errorf("%s: wrapper forwards to %s, record target is %s", key, callee, want)
			}
		} else {
			if r["unsupported"] != reason {
				t.Errorf("%s: stub cause differs from the record's", key)
			}
			sig, ok := r["sig"].(map[string]any)
			if !ok {
				t.Errorf("%s: stub record without sig", key)
				continue
			}
			if fmtJSON(sig["params"]) != fmtJSON(paramTypes(mm["params"])) || fmtJSON(sig["results"]) != fmtJSON(paramTypes(mm["results"])) || sig["variadic"] != mm["variadic"] {
				t.Errorf("%s: record sig %s differs from the stub's signature", key, fmtJSON(sig))
			}
		}
	}
	if paired != len(recs) {
		t.Errorf("%d records for %d wrappers+stubs", len(recs), paired)
	}
}

func paramTypes(v any) []any {
	out := []any{}
	for _, p := range v.([]any) {
		out = append(out, p.(map[string]any)["type"])
	}
	return out
}

const promotionShapesSrc = `package main

type base struct{ n int }

func (b base) val() int { return b.n }
func (b *base) inc()    { b.n++ }

type mid struct{ base }
type outer struct{ *mid }
type pouter struct{ *base }
type solo struct{ base }
type valuer interface{ val() int }
type incer interface{ inc() }
type wrapI struct{ valuer }

func main() {
	var v valuer = mid{}
	var i incer = &mid{}
	var v2 valuer = outer{}
	var i2 incer = outer{}
	var v3 valuer = pouter{}
	var i3 incer = pouter{}
	var w valuer = wrapI{v}
	var i4 incer = &solo{}
	_, _, _, _, _, _, _, _ = v, i, v2, i2, v3, i3, w, i4
}
`

func TestPromotionRecordShapes(t *testing.T) {
	program, err := emitSource(t, promotionShapesSrc)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	recs := promotionRecords(t, program)
	val := methodTarget("main.base", "val", "main")
	inc := methodTarget("main.base", "inc", "main")
	// value embed: the value method is in both sets, the pointer method in *mid only
	expectRecord(t, recs, "main.mid.val", false, []map[string]any{hop("main.mid", "base", false)}, "asIs", val)
	expectRecord(t, recs, "main.mid.inc", true, []map[string]any{hop("main.mid", "base", false)}, "addr", inc)
	// pointer embed then value embed: both methods in both sets; the pointer hop supplies the address
	two := []map[string]any{hop("main.outer", "mid", true), hop("main.mid", "base", false)}
	expectRecord(t, recs, "main.outer.val", false, two, "asIs", val)
	expectRecord(t, recs, "main.outer.inc", false, two, "addr", inc)
	// pointer embed of the declaring type: the value method dereferences, the pointer method takes the field as is
	one := []map[string]any{hop("main.pouter", "base", true)}
	expectRecord(t, recs, "main.pouter.val", false, one, "deref", val)
	expectRecord(t, recs, "main.pouter.inc", false, one, "asIs", inc)
	// an embedded interface field
	expectRecord(t, recs, "main.wrapI.val", false, []map[string]any{hop("main.wrapI", "valuer", false)}, "asIs", map[string]any{"iface": "main.valuer"})
	// a *T-only entry
	expectRecord(t, recs, "main.solo.inc", true, []map[string]any{hop("main.solo", "base", false)}, "addr", inc)
	expectRecord(t, recs, "main.solo.val", false, []map[string]any{hop("main.solo", "base", false)}, "asIs", val)
	for _, r := range recs {
		if _, stub := r["unsupported"]; stub {
			t.Errorf("%s.%s: no stub expected", r["type"], r["member"].(memberID).Name)
		}
		if _, sig := r["sig"]; sig {
			t.Errorf("%s.%s: no sig expected", r["type"], r["member"].(memberID).Name)
		}
	}
	checkPairing(t, program, recs)
}

const promotionSyncSrc = `package main

import "sync"

type locked struct {
	sync.Mutex
	n int
}
type locker interface {
	Lock()
	Unlock()
}

func main() {
	var l locker = &locked{}
	l.Lock()
	l.Unlock()
}
`

// TestPromotionRecordSyncStub — the promoted sync-primitive methods are
// declaration-only stubs (syncPromotedStub); their records carry the
// stub's cause and signature, present together, and target the primitive's
// method entry.
func TestPromotionRecordSyncStub(t *testing.T) {
	program, err := emitSource(t, promotionSyncSrc)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	recs := promotionRecords(t, program)
	path := []map[string]any{hop("main.locked", "Mutex", false)}
	for _, name := range []string{"Lock", "Unlock", "TryLock"} {
		r := expectRecord(t, recs, "main.locked."+name, true, path, "addr", methodTarget("sync.Mutex", name, ""))
		reason, _ := r["unsupported"].(string)
		if !strings.HasPrefix(reason, "promoted sync-primitive method sync.Mutex."+name) {
			t.Errorf("locked.%s: unsupported = %q", name, reason)
		}
		sig, ok := r["sig"].(map[string]any)
		if !ok {
			t.Fatalf("locked.%s: no sig", name)
		}
		if sig["id"].(memberID) != (memberID{Name: name}) || len(sig["params"].([]any)) != 0 || sig["variadic"] != false {
			t.Errorf("locked.%s: sig = %s", name, fmtJSON(sig))
		}
		wantResults := 0
		if name == "TryLock" {
			wantResults = 1
		}
		if len(sig["results"].([]any)) != wantResults {
			t.Errorf("locked.%s: sig results = %s", name, fmtJSON(sig["results"]))
		}
	}
	if len(recs) != 3 {
		t.Errorf("records = %v, want the three Mutex methods", recordKeys(recs))
	}
	checkPairing(t, program, recs)
}

const promotionFR23Src = `package main

import "iter"

type Bag struct{ items []int }

func (b Bag) All() iter.Seq[int] {
	return func(yield func(int) bool) {
		for _, v := range b.items {
			if !yield(v) {
				return
			}
		}
	}
}

type Outer struct{ Bag }
type Iterable interface{ All() iter.Seq[int] }

func main() {
	var it Iterable = Outer{}
	_ = it
}
`

// TestPromotionRecordFR23Stub — a promoted method whose signature
// instantiates an imported generic (FR-23) is a signature-carrying stub
// (promotedSigStub); its record is the stub's cause and opaque-mode
// signature, targeting the declared method.
func TestPromotionRecordFR23Stub(t *testing.T) {
	program, err := emitSource(t, promotionFR23Src)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	recs := promotionRecords(t, program)
	r := expectRecord(t, recs, "main.Outer.All", false, []map[string]any{hop("main.Outer", "Bag", false)}, "asIs", methodTarget("main.Bag", "All", ""))
	reason, _ := r["unsupported"].(string)
	if !strings.Contains(reason, "FR-23") || !strings.HasPrefix(reason, "promoted method main.Outer.All") {
		t.Errorf("Outer.All: unsupported = %q", reason)
	}
	sig := r["sig"].(map[string]any)
	if len(sig["results"].([]any)) != 1 || fmtJSON(sig["results"].([]any)[0]) != `{"kind":"named","name":"iter.Seq[int]"}` {
		t.Errorf("Outer.All: sig results = %s", fmtJSON(sig["results"]))
	}
	checkPairing(t, program, recs)
}

const promotionGenericSrc = `package main

type box[T any] struct{ v T }

func (b box[T]) get() T { return b.v }

type holder struct{ box[int] }
type getter interface{ get() int }

func main() {
	var g getter = holder{box[int]{7}}
	println(g.get())
}
`

// TestPromotionRecordGenericInstantiation — an instantiated struct's
// records come from the instantiated method set in the same pass as its
// wrapper (design §2 S10): holder.get targets the box[int] stencil's method.
func TestPromotionRecordGenericInstantiation(t *testing.T) {
	program, err := emitSource(t, promotionGenericSrc)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	recs := promotionRecords(t, program)
	r, ok := recs["main.holder.get"]
	if !ok {
		t.Fatalf("no record for main.holder.get (have %v)", recordKeys(recs))
	}
	path := r["path"].([]any)
	if len(path) != 1 || path[0].(map[string]any)["owner"] != "main.holder" || path[0].(map[string]any)["field"] != "box" || path[0].(map[string]any)["ptr"] != false {
		t.Errorf("holder.get path = %s", fmtJSON(path))
	}
	target := r["target"].(map[string]any)["method"].(string)
	// The target names the instantiated stencil's method: a method entry
	// with that callable key exists on the wire, on a recvType other than
	// the carrier, with member `get`.
	found := false
	for _, m := range program["methods"].([]any) {
		mm := m.(map[string]any)
		if methodFuncKey(mm["recvType"].(string), mm["id"].(memberID)) == target {
			found = true
			if mm["recvType"] == "main.holder" || mm["id"].(memberID).Name != "get" || mm["wrapper"] == true {
				t.Errorf("holder.get target %s resolves to %s.%s (wrapper=%v)", target, mm["recvType"], mm["id"].(memberID).Name, mm["wrapper"])
			}
			if !strings.Contains(mm["recvType"].(string), "box") {
				t.Errorf("holder.get target recvType %s does not name the box stencil", mm["recvType"])
			}
		}
	}
	if !found {
		t.Errorf("holder.get target %s is not a method on the wire", target)
	}
	checkPairing(t, program, recs)
}

// TestPromotionRecordsEmptyWhenNonePromoted — a package with no promoted
// entry still carries the REQUIRED key, as an empty array (never null).
func TestPromotionRecordsEmptyWhenNonePromoted(t *testing.T) {
	program, err := emitSource(t, "package main\n\ntype T struct{ n int }\n\nfunc (t T) M() int { return t.n }\n\nfunc main() { println(T{1}.M()) }\n")
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	b, err := json.Marshal(program["promotions"])
	if err != nil {
		t.Fatal(err)
	}
	if string(b) != "[]" {
		t.Fatalf("promotions = %s, want []", b)
	}
}
