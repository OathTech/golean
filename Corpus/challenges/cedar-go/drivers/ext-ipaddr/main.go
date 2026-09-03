// cedar-go census driver: the `ipaddr` extension type — parse (net/netip
// inside), predicates, range containment, print. Self-checking.
// [AGENT] 2026-09-03.
package main

import "cedargo/types"

func censusMain() {
	host, err := types.ParseIPAddr("192.168.1.10")
	if err != nil {
		panic("parse host: " + err.Error())
	}
	net, err := types.ParseIPAddr("192.168.1.0/24")
	if err != nil {
		panic("parse net: " + err.Error())
	}
	if !host.IsIPv4() || host.IsIPv6() || host.IsLoopback() {
		panic("v4 predicates")
	}
	if !net.Contains(host) || host.Contains(net) {
		panic("containment")
	}
	lo, _ := types.ParseIPAddr("127.0.0.1")
	if !lo.IsLoopback() {
		panic("loopback")
	}
	six, err := types.ParseIPAddr("::1")
	if err != nil || !six.IsIPv6() || !six.IsLoopback() {
		panic("v6 loopback")
	}
	if host.String() != "192.168.1.10" || net.String() != "192.168.1.0/24" {
		panic("string forms")
	}
	if string(host.MarshalCedar()) != `ip("192.168.1.10")` {
		panic("cedar form")
	}
	if _, err := types.ParseIPAddr("not-an-ip"); err == nil {
		panic("expected parse error")
	}
}

func main() { censusMain() }
