package main

import (
	_golean_os "os"
	_golean_debug "runtime/debug"
)

func _goleanSetupCrash() {
	f, err := _golean_os.OpenFile("oracle.crash", _golean_os.O_WRONLY|_golean_os.O_TRUNC, 0600)
	if err != nil { _golean_os.Exit(78) }
	if err := _golean_debug.SetCrashOutput(f, _golean_debug.CrashOptions{}); err != nil { _golean_os.Exit(78) }
	if err := f.Close(); err != nil { _golean_os.Exit(78) }
	if err := _golean_os.WriteFile("oracle.registered", []byte("registered\n"), 0600); err != nil { _golean_os.Exit(78) }
}
