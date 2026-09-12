package main

// Excluded on linux/amd64 by the _linux_arm64 suffix: the OS half matches,
// the ARCH half does not (go/build goodOSArchFile checks both).
func init() { fromLinuxArm64 = 2 }
