// cedar-go census driver: the VALIDATOR / typechecker path — schema in
// Cedar schema text -> Resolve -> validate.New -> Policy on a well-typed
// and an ill-typed policy. Self-checking. [AGENT] 2026-09-03.
package main

import (
	"cedargo/ast"
	"cedargo/types"
	xast "cedargo/x/exp/ast"
	"cedargo/x/exp/schema"
	"cedargo/x/exp/schema/validate"
)

const schemaCedar = `
entity User { age: Long };
entity Album;
entity Photo in [Album] { name: String };
action view appliesTo { principal: [User], resource: [Photo], context: { demo: Bool } };
`

func censusMain() {
	var s schema.Schema
	if err := s.UnmarshalCedar([]byte(schemaCedar)); err != nil {
		panic("schema parse: " + err.Error())
	}
	r, err := s.Resolve()
	if err != nil {
		panic("schema resolve: " + err.Error())
	}
	v := validate.New(r)

	good := ast.Permit().PrincipalIs("User").ActionEq(types.NewEntityUID("Action", "view")).ResourceIs("Photo").
		When(ast.Principal().Access("age").GreaterThan(ast.Long(17)).And(ast.Context().Access("demo")))
	if err := v.Policy("good", (*xast.Policy)(good)); err != nil {
		panic("well-typed policy rejected: " + err.Error())
	}
	bad := ast.Permit().PrincipalIs("User").ActionEq(types.NewEntityUID("Action", "view")).ResourceIs("Photo").
		When(ast.Principal().Access("age").Add(ast.String("x")).Equal(ast.Long(1)))
	if err := v.Policy("bad", (*xast.Policy)(bad)); err == nil {
		panic("ill-typed policy accepted")
	}
	req := types.Request{Principal: types.NewEntityUID("User", "alice"), Action: types.NewEntityUID("Action", "view"),
		Resource: types.NewEntityUID("Photo", "p"), Context: types.NewRecord(types.RecordMap{"demo": types.True})}
	if err := v.Request(req); err != nil {
		panic("well-typed request rejected: " + err.Error())
	}
}

func main() { censusMain() }
