// cedar-go census driver: the EVALUATOR path only — policies built through
// the ast builder (no parser, no JSON), entities built programmatically,
// cedar.Authorize. Self-checking: silent on success, panics on any wrong
// decision. [AGENT] 2026-09-03.
package main

import (
	cedar "cedargo"
	"cedargo/ast"
	"cedargo/types"
)

func censusMain() {
	alice := types.NewEntityUID("User", "alice")
	bob := types.NewEntityUID("User", "bob")
	view := types.NewEntityUID("Action", "view")
	album := types.NewEntityUID("Album", "jane_vacation")
	photo := types.NewEntityUID("Photo", "VacationPhoto94.jpg")

	permit := ast.Permit().PrincipalEq(alice).ActionEq(view).ResourceIn(album).
		When(ast.Context().Access("demo").Equal(ast.True()))
	forbid := ast.Forbid().PrincipalEq(bob)

	ps := cedar.NewPolicySet()
	ps.Add("policy0", cedar.NewPolicyFromAST(permit))
	ps.Add("policy1", cedar.NewPolicyFromAST(forbid))

	entities := types.EntityMap{
		photo: types.Entity{UID: photo, Parents: types.NewEntityUIDSet(album), Attributes: types.NewRecord(types.RecordMap{})},
		alice: types.Entity{UID: alice, Attributes: types.NewRecord(types.RecordMap{"age": types.Long(18)})},
	}
	req := types.Request{Principal: alice, Action: view, Resource: photo,
		Context: types.NewRecord(types.RecordMap{"demo": types.True})}

	dec, diag := cedar.Authorize(ps, entities, req)
	if dec != types.Allow {
		panic("expected allow for alice")
	}
	if len(diag.Reasons) != 1 || diag.Reasons[0].PolicyID != "policy0" {
		panic("expected determining policy policy0")
	}
	if len(diag.Errors) != 0 {
		panic("expected no evaluation errors")
	}

	req.Principal = bob
	dec, diag = cedar.Authorize(ps, entities, req)
	if dec != types.Deny || len(diag.Reasons) != 1 || diag.Reasons[0].PolicyID != "policy1" {
		panic("expected forbid-trumps for bob")
	}

	req.Principal = types.NewEntityUID("User", "carol")
	dec, diag = cedar.Authorize(ps, entities, req)
	if dec != types.Deny || len(diag.Reasons) != 0 {
		panic("expected default deny for carol")
	}

	// Context missing the attribute: the permit ERRORS (not a match) and
	// the decision is Deny with one erroring policy recorded.
	req.Principal = alice
	req.Context = types.NewRecord(types.RecordMap{})
	dec, diag = cedar.Authorize(ps, entities, req)
	if dec != types.Deny || len(diag.Errors) != 1 || diag.Errors[0].PolicyID != "policy0" {
		panic("expected erroring permit to deny")
	}
}

func main() { censusMain() }
