import GoLean.GoCore.Machine
import GoLean.CLI
open GoLean GoLean.GoCore GoLean.GoCore.Machine
example : IntKind.uintptr ≠ IntKind.uint64 := by decide
example : IntKind.uintptr.bits? = some 64 := rfl
example (p : Platform) : IntKind.uintptr.bitsAt p = some (8 * p.wordBytes) := rfl
example : IntKind.uintptr.signed = false := rfl
example : IntKind.uintptr.normalize (-1) = 18446744073709551615 := by decide +kernel
example : IntKind.compatibleResult .uintptr .uint64 = none := rfl
example : atomicKindOk .uintptr = true := rfl
example : atomicKindOk .uint8 = false := rfl
example : atomicCompute .add .uintptr 18446744073709551615 [.int 1 .uintptr] = .ok (some 0, .int 0 .uintptr) := by rfl
example : (Ty.int .uintptr == Ty.int .uint64) = false := rfl
