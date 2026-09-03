// cedar-go census driver: evaluator operator coverage — arithmetic,
// comparison, `has`, `like` (types.Pattern), set contains, entity `in`
// through the hierarchy, if-then-else — all via the ast builder.
// Self-checking. [AGENT] 2026-09-03.
package main

import (
	cedar "cedargo"
	"cedargo/ast"
	"cedargo/types"
)

func decide(cond ast.Node, entities types.EntityMap, req types.Request) types.Decision {
	p := ast.Permit().When(cond)
	ps := cedar.NewPolicySet()
	ps.Add("p", cedar.NewPolicyFromAST(p))
	dec, diag := cedar.Authorize(ps, entities, req)
	if len(diag.Errors) != 0 {
		panic("unexpected evaluation error: " + diag.Errors[0].Message)
	}
	return dec
}

func expect(name string, cond ast.Node, entities types.EntityMap, req types.Request, want types.Decision) {
	if got := decide(cond, entities, req); got != want {
		panic("case " + name + ": wrong decision")
	}
}

func censusMain() {
	alice := types.NewEntityUID("User", "alice")
	view := types.NewEntityUID("Action", "view")
	album := types.NewEntityUID("Album", "jane_vacation")
	photo := types.NewEntityUID("Photo", "VacationPhoto94.jpg")
	entities := types.EntityMap{
		photo: types.Entity{UID: photo, Parents: types.NewEntityUIDSet(album),
			Attributes: types.NewRecord(types.RecordMap{"name": types.String("VacationPhoto94.jpg"), "size": types.Long(2048)})},
		alice: types.Entity{UID: alice, Attributes: types.NewRecord(types.RecordMap{
			"age":    types.Long(18),
			"groups": types.NewSet(types.String("friends"), types.String("family")),
		})},
	}
	req := types.Request{Principal: alice, Action: view, Resource: photo,
		Context: types.NewRecord(types.RecordMap{"n": types.Long(7)})}

	expect("arith", ast.Context().Access("n").Multiply(ast.Long(6)).Add(ast.Long(1)).Equal(ast.Long(43)), entities, req, types.Allow)
	expect("cmp", ast.Principal().Access("age").GreaterThanOrEqual(ast.Long(18)), entities, req, types.Allow)
	expect("cmp-neg", ast.Principal().Access("age").LessThan(ast.Long(18)), entities, req, types.Deny)
	expect("has", ast.Principal().Has("age").And(ast.Not(ast.Principal().Has("email"))), entities, req, types.Allow)
	expect("like", ast.Resource().Access("name").Like(types.NewPattern("Vacation", types.Wildcard{}, ".jpg")), entities, req, types.Allow)
	expect("like-neg", ast.Resource().Access("name").Like(types.NewPattern("Work", types.Wildcard{})), entities, req, types.Deny)
	expect("contains", ast.Principal().Access("groups").Contains(ast.String("family")), entities, req, types.Allow)
	expect("in-hierarchy", ast.Resource().In(ast.EntityUID("Album", "jane_vacation")), entities, req, types.Allow)
	expect("is", ast.Resource().Is("Photo"), entities, req, types.Allow)
	expect("ite", ast.IfThenElse(ast.Context().Access("n").GreaterThan(ast.Long(5)), ast.True(), ast.False()), entities, req, types.Allow)
	expect("short-circuit", ast.False().And(ast.Context().Access("missing").Equal(ast.Long(1))), entities, req, types.Deny)
	expect("set-literal", ast.Set(ast.Long(1), ast.Long(2)).Contains(ast.Long(2)), entities, req, types.Allow)
}

func main() { censusMain() }
