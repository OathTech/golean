package main

// spec#Basic_interfaces block Basic_interfaces-5-0c73e0fa (the Locker
// interface) + block Basic_interfaces-6-30e0b4a6 (func (p T) Lock/Unlock):
// any type whose method set contains Lock and Unlock implements Locker; a T
// value assigned to a Locker variable dispatches to T's methods. The spec's
// elided method bodies are realized as recorders.

type Locker interface {
	Lock()
	Unlock()
}

type T struct{}

var lockLog string

func (p T) Lock()   { lockLog += "L" }
func (p T) Unlock() { lockLog += "U" }

func lockerSatisfaction() string {
	lockLog = ""
	var l Locker = T{} // T implements Locker
	l.Lock()
	l.Unlock()
	return lockLog
}
