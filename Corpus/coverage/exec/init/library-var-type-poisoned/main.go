// FR-24 (2026-09-04): a REACHED source-through library package-level var
// whose TYPE does not lower — encoding/binary's `var structSize sync.Map`
// (dataSize's cache, reached through Write/Size) — is POISONED per
// declaration: its cell is the `$poisoned` placeholder and dataSize is an
// H-3 stub naming the var (`package-level var encoding/binary.structSize:
// type sync.Map does not lower (...) — FR-24 poison`; recorded in
// docs/evidence/2026-09-04_fr24-fr25/binary-quarantine-trace.txt). Before FR-24
// the mere reach of binary.Write took the whole export down (cedar-go
// types/record.go:35, census addendum §9.2).
//
// TODAY every row here is still red at frontend-export, on the NEXT kill
// behind the poisoned var (rowed FR-25, same evidence dir): `sizeof(t
// reflect.Type)` LOWERS, and reflect.Type's requirement list carries
// `OverflowComplex(complex128)`, which the interface declaration pass
// refuses whole ("basic type complex128"). When FR-25 closes:
//   sibling      flips PASS — the package lowers beside the poisoned var
//                (PutUint64: the byte-order path, untouched by structSize);
//   writeInt     stays red BY NAME at Write: the intDataSize FAST path
//                never touches structSize, but Write's SLOW path (the same
//                body) is reflect, so Write is ONE H-3 stub on
//                `reflect.Indirect` — the register's encoding/binary row
//                already says so ("Read/Write/Size are reflect and refuse
//                by name"); the fast path is not separately reachable;
//   writeStruct  stays red at the same Write stub (dataSize's own
//                structSize refusal sits behind it, never reached first);
//   sizeInt      stays red at Size (type-switch fast path, reflect
//                fallback in the same body → one stub).
package main

import (
	"bytes"
	"encoding/binary"
)

type pair struct {
	A uint32
	B uint32
}

func sibling() int {
	var hb [8]byte
	binary.LittleEndian.PutUint64(hb[:], 0x0102030405060708)
	return int(hb[0])*100 + int(hb[7])
}

func writeInt() int {
	var buf bytes.Buffer
	if err := binary.Write(&buf, binary.LittleEndian, uint64(7)); err != nil {
		return -1
	}
	return buf.Len()
}

func writeStruct() int {
	var buf bytes.Buffer
	if err := binary.Write(&buf, binary.LittleEndian, pair{A: 1, B: 2}); err != nil {
		return -1
	}
	return buf.Len()
}

func sizeInt() int { return binary.Size(int32(1)) }

func main() { println(sibling(), writeInt(), writeStruct(), sizeInt()) }
