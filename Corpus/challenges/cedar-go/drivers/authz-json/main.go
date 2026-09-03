// cedar-go census driver: the JSON codec path — entities via
// EntityMap.UnmarshalJSON, policies via PolicySet.UnmarshalJSON (both
// encoding/json inside the library), then Authorize. Self-checking.
// [AGENT] 2026-09-03.
package main

import (
	cedar "cedargo"
	"cedargo/types"
)

const entitiesJSON = `[
  { "uid": { "type": "User", "id": "alice" }, "attrs": { "age": 18 }, "parents": [] },
  { "uid": { "type": "Photo", "id": "VacationPhoto94.jpg" }, "attrs": {},
    "parents": [{ "type": "Album", "id": "jane_vacation" }] }
]`

const policiesJSON = `{ "staticPolicies": { "policy0": {
  "effect": "permit",
  "principal": { "op": "==", "entity": { "type": "User", "id": "alice" } },
  "action": { "op": "==", "entity": { "type": "Action", "id": "view" } },
  "resource": { "op": "in", "entity": { "type": "Album", "id": "jane_vacation" } },
  "conditions": [] } } }`

func censusMain() {
	var entities types.EntityMap
	if err := entities.UnmarshalJSON([]byte(entitiesJSON)); err != nil {
		panic("entities: " + err.Error())
	}
	var ps cedar.PolicySet
	if err := ps.UnmarshalJSON([]byte(policiesJSON)); err != nil {
		panic("policies: " + err.Error())
	}
	req := types.Request{
		Principal: types.NewEntityUID("User", "alice"),
		Action:    types.NewEntityUID("Action", "view"),
		Resource:  types.NewEntityUID("Photo", "VacationPhoto94.jpg"),
		Context:   types.NewRecord(types.RecordMap{}),
	}
	dec, diag := cedar.Authorize(&ps, entities, req)
	if dec != types.Allow || len(diag.Reasons) != 1 || diag.Reasons[0].PolicyID != "policy0" {
		panic("expected allow by policy0")
	}
	out, err := entities.MarshalJSON()
	if err != nil || len(out) == 0 {
		panic("entities marshal")
	}
}

func main() { censusMain() }
