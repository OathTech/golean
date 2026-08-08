// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/replicated_disk.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type Block struct {
	Value uint64
}

const Disk1 uint64 = 0
const Disk2 uint64 = 0
const DiskSize uint64 = 1000

// TwoDiskWrite is a dummy function to represent the base layer's disk write
func TwoDiskWrite(diskId uint64, a uint64, v Block) bool {
	return true
}

// TwoDiskRead is a dummy function to represent the base layer's disk read
func TwoDiskRead(diskId uint64, a uint64) (Block, bool) {
	return Block{Value: 0}, true
}

// TwoDiskLock is a dummy function to represent locking an address in the
// base layer
func TwoDiskLock(a uint64) {}

// TwoDiskUnlock is a dummy function to represent unlocking an address in the
// base layer
func TwoDiskUnlock(a uint64) {}

func ReplicatedDiskRead(a uint64) Block {
	TwoDiskLock(a)
	v, ok := TwoDiskRead(Disk1, a)
	if ok {
		TwoDiskUnlock(a)
		return v
	}
	v2, _ := TwoDiskRead(Disk2, a)
	// we assume both disks cannot fail
	TwoDiskUnlock(a)
	return v2
}

func ReplicatedDiskWrite(a uint64, v Block) {
	TwoDiskLock(a)
	TwoDiskWrite(Disk1, a, v)
	TwoDiskWrite(Disk2, a, v)
	TwoDiskUnlock(a)
}

func ReplicatedDiskRecover() {
	for a := uint64(0); ; {
		if a > DiskSize {
			break
		}
		v, ok := TwoDiskRead(Disk1, a)
		if ok {
			TwoDiskWrite(Disk2, a, v)
		}
		a = a + 1
		continue
	}
}

// --- GoLean harness ---
// Authored wrapper.

func goleanReplicatedDisk() int {
	ReplicatedDiskWrite(3, Block{Value: 9})
	v := ReplicatedDiskRead(3)
	ReplicatedDiskRecover()
	return int(v.Value) + 1
}

func main() {}
