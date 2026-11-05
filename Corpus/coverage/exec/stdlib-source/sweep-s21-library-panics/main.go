package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group J: the library panics the existing rows omit, verbatim texts from the pinned bodies; the runtime panics inside
// library bodies reached by user inputs (nil receivers, short buffers).
import (
	"bytes"
	"encoding/binary"
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"
)

func slicesMinEmpty() int    { return slices.Min([]int{}) }
func slicesMaxEmpty() string { var s []string; return slices.Max(s) }
func slicesMinFuncEmpty() int {
	return slices.MinFunc([]int{}, func(a, b int) int { return a - b })
}
func slicesMaxFuncEmpty() int {
	return slices.MaxFunc([]int{}, func(a, b int) int { return a - b })
}
func slicesGrowNegative() int       { return len(slices.Grow([]int{1}, -1)) }
func slicesRepeatOverflow() int     { return len(slices.Repeat([]int{1, 2}, 9223372036854775807)) }
func bytesRepeatOverflow() int      { return len(bytes.Repeat([]byte("ab"), 9223372036854775807)) }
func appendIntIllegalBase() int     { return len(strconv.AppendInt(nil, 5, 1)) }
func formatUintIllegalBase() string { return strconv.FormatUint(5, 37) }
func putUvarintShort() int          { return binary.PutUvarint(make([]byte, 1), 300) }
func encodeRuneShort() int          { return utf8.EncodeRune(make([]byte, 1), '\u00e9') }
func nilBuilderWrite() int {
	var b *strings.Builder
	n, _ := b.WriteString("x")
	return n
}
func nilBufferLen() int {
	var b *bytes.Buffer
	return b.Len()
}
func bigEndianNil() uint64 { return binary.BigEndian.Uint64(nil) }
func putUint32Short() int  { b := make([]byte, 3); binary.LittleEndian.PutUint32(b, 1); return len(b) }

func main() {
	slicesMinEmpty()
	slicesMaxEmpty()
	slicesMinFuncEmpty()
	slicesMaxFuncEmpty()
	slicesGrowNegative()
	slicesRepeatOverflow()
	bytesRepeatOverflow()
	appendIntIllegalBase()
	formatUintIllegalBase()
	putUvarintShort()
	encodeRuneShort()
	nilBuilderWrite()
	nilBufferLen()
	bigEndianNil()
	putUint32Short()
}
