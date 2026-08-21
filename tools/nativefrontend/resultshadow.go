// Named-result SHADOW renaming — BUG fix, W4.3 (docs/raft-w43-log.md,
// wave 6; found by the trace differential's rendered tier on
// confchange_v2_add_double_{auto,implicit} and minimized to
// artifacts/w43/probe-autoleave).
//
// THE DEFECT. The wire carries variable NAMES, and a function's named
// results are frame locals the machine writes at `return` and reads at
// frame exit BY NAME. A function-local variable DECLARED WITH THE SAME
// NAME as a named result — upstream raft's ConfChangeV2.EnterJoint does
// exactly this (`func ... (autoLeave bool, ok bool)` with an inner
// `var autoLeave bool`) — therefore ALIASES the result slot at the
// return/exit seam: the return's write lands on the lexically-nearest
// (inner) binding while the frame exit reads the outer result local,
// yielding a SILENT WRONG ANSWER (autoLeave=false where gc says true;
// go/types resolves the source correctly, the wire's name channel
// cannot carry the distinction).
//
// THE FIX. Emit-time RENAMING, keyed by go/types OBJECT IDENTITY: every
// function-local variable definition whose name collides with a named
// result of the ENCLOSING function is renamed `<name>$shadow<n>`, and
// every read/write/declare/address-of of that OBJECT follows the rename
// (the four local-name emission sites consult e.localRenames). Nested
// function literals are pruned from the scan — their frames have their
// own result slots and their own scan; a lit-local shadowing an OUTER
// result can only reach the outer frame through the capture machinery,
// which is object-keyed already.
//
// FAIL-CLOSED GUARD: the scan REFUSES (never renames) a colliding
// definition arising from a construct whose emission path is not among
// the four patched sites (range clauses, type-switch guards, comma-ok
// receive targets, parameters of the function itself...): a rename such
// a path did not follow would declare under one name and read under
// another — a visible decode failure at best, an alias at worst. The
// refusal names the construct; widening the admissible set moves a
// shape from refused to renamed with its own guardrail row first.

package main

import (
	"go/ast"
	"go/token"
	"go/types"
)

// resultShadowScan (re)builds e.localRenames for the function body
// about to be emitted under e.curResults.
func (e *emitter) resultShadowScan(body ast.Node) error {
	e.localRenames = nil
	if body == nil || e.curResults == nil {
		return nil
	}
	resultNames := map[string]bool{}
	for i := 0; i < e.curResults.Len(); i++ {
		n := e.curResults.At(i).Name()
		if n != "" && n != "_" {
			resultNames[n] = true
		}
	}
	if len(resultNames) == 0 {
		return nil
	}
	// Pass 1: the ADMISSIBLE definition sites (plain var specs and :=
	// targets — the declaration forms the patched emission sites cover),
	// nested function literals pruned.
	admissible := map[types.Object]bool{}
	ast.Inspect(body, func(n ast.Node) bool {
		switch v := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.ValueSpec:
			for _, nm := range v.Names {
				if obj := e.info.Defs[nm]; obj != nil {
					admissible[obj] = true
				}
			}
		case *ast.AssignStmt:
			if v.Tok == token.DEFINE {
				for _, l := range v.Lhs {
					if id, isIdent := l.(*ast.Ident); isIdent {
						if obj := e.info.Defs[id]; obj != nil {
							admissible[obj] = true
						}
					}
				}
			}
		}
		return true
	})
	// Pass 2: every colliding local-var definition either gets a rename
	// (admissible) or refuses (fail closed).
	seq := 0
	var serr error
	ast.Inspect(body, func(n ast.Node) bool {
		if _, isLit := n.(*ast.FuncLit); isLit {
			return false
		}
		id, isIdent := n.(*ast.Ident)
		if !isIdent || !resultNames[id.Name] || serr != nil {
			return true
		}
		obj := e.info.Defs[id]
		v, isVar := obj.(*types.Var)
		if obj == nil || !isVar || v.IsField() {
			return true
		}
		if !admissible[obj] {
			serr = unsup("local %s shadows the named result %s in a construct outside the rename set (range/type-switch/receive binding) — fail closed, widen with a guardrail row first", id.Name, id.Name)
			return false
		}
		if e.localRenames == nil {
			e.localRenames = map[types.Object]string{}
		}
		e.localRenames[obj] = id.Name + "$shadow" + itoa(seq)
		seq++
		return true
	})
	return serr
}

// localRename reports the emission name for a resolved local object.
func (e *emitter) localRename(obj types.Object, name string) string {
	if obj == nil || e.localRenames == nil {
		return name
	}
	if rn, ok := e.localRenames[obj]; ok {
		return rn
	}
	return name
}
