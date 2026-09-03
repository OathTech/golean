// cedar-go census driver: Cedar text -> Policy.MarshalJSON -> Policy.
// UnmarshalJSON -> MarshalCedar, checked against the direct printer
// output. Self-checking. [AGENT] 2026-09-03.
package main

import (
	cedar "cedargo"
)

const policyCedar = `permit (
	principal == User::"alice",
	action in [Action::"view", Action::"edit"],
	resource
) when { resource.owner == principal && context.count < 10 } unless { principal.banned };
`

func censusMain() {
	var p cedar.Policy
	if err := p.UnmarshalCedar([]byte(policyCedar)); err != nil {
		panic("parse: " + err.Error())
	}
	j, err := p.MarshalJSON()
	if err != nil {
		panic("marshal json: " + err.Error())
	}
	var q cedar.Policy
	if err := q.UnmarshalJSON(j); err != nil {
		panic("unmarshal json: " + err.Error())
	}
	if string(q.MarshalCedar()) != string(p.MarshalCedar()) {
		panic("json round trip changed the policy")
	}
	if p.Effect() != cedar.Permit {
		panic("effect")
	}
}

func main() { censusMain() }
