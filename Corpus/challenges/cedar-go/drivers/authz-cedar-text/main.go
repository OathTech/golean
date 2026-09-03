// cedar-go census driver: the PARSER path — a policy in Cedar text through
// Policy.UnmarshalCedar (internal/parser), then Authorize. Self-checking.
// [AGENT] 2026-09-03.
package main

import (
	cedar "cedargo"
	"cedargo/types"
)

const policyCedar = `permit (
	principal == User::"alice",
	action == Action::"view",
	resource in Album::"jane_vacation"
) when { context.demo == true };
`

func censusMain() {
	var policy cedar.Policy
	if err := policy.UnmarshalCedar([]byte(policyCedar)); err != nil {
		panic("policy unmarshal error: " + err.Error())
	}
	ps := cedar.NewPolicySet()
	ps.Add("policy0", &policy)

	alice := types.NewEntityUID("User", "alice")
	album := types.NewEntityUID("Album", "jane_vacation")
	photo := types.NewEntityUID("Photo", "VacationPhoto94.jpg")
	entities := types.EntityMap{
		photo: types.Entity{UID: photo, Parents: types.NewEntityUIDSet(album)},
	}
	req := types.Request{Principal: alice, Action: types.NewEntityUID("Action", "view"), Resource: photo,
		Context: types.NewRecord(types.RecordMap{"demo": types.True})}
	dec, diag := cedar.Authorize(ps, entities, req)
	if dec != types.Allow || len(diag.Reasons) != 1 {
		panic("expected allow")
	}
	// Round-trip through the printer.
	out := policy.MarshalCedar()
	var again cedar.Policy
	if err := again.UnmarshalCedar(out); err != nil {
		panic("re-parse error: " + err.Error())
	}
	if string(again.MarshalCedar()) != string(out) {
		panic("printer not idempotent")
	}
}

func main() { censusMain() }
