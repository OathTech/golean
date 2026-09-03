#!/usr/bin/env bash
# gen.sh — build and run the ParseUint SHIM-vs-strconv fuzz (Fields-standard
# validation of the retained, re-bodied shim; stdlib-source-1, 2026-09-03).
# Extracts the shim's SOURCE verbatim from tools/nativefrontend/stdlibshim.go
# (the text the frontend injects — no copy to drift), appends a harness that
# calls it side by side with the real strconv.ParseUint under the pinned
# toolchain, and compares (value, err == nil, err.Error(), *NumError fields,
# sentinel identity) over N random trials. Run from the repo root:
#   docs/evidence/2026-09-03_stdlib-source-1/parseuint-fuzz/gen.sh [N] [seed]
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
cd "$ROOT"
N="${1:-100000}"; SEED="${2:-20260903}"
OUT="artifacts/stdlib-source-1-parseuint-fuzz"; mkdir -p "$OUT"
{
  echo 'package main'
  echo 'import ("errors"; "fmt"; "math/rand"; "os"; "strconv")'
  echo 'var refused int'
  echo 'func goleanShimUnsupported(msg string) { refused++; panic("refused: " + msg) }'
  # the shim source: from the map entry's opening backtick to the closing "`,"
  awk '/^\tstrconvParseUintShimName: `$/{f=1;next} f&&/^`,$/{exit} f' tools/nativefrontend/stdlibshim.go
  cat <<'HARNESS'
func trial(s string, base, bitSize int) (mismatch string) {
	defer func() {
		if r := recover(); r != nil {
			mismatch = "" // a recorded-bound refusal (base 0 / bitSize > 64): counted, not a mismatch
		}
	}()
	wv, werr := strconv.ParseUint(s, base, bitSize)
	sv, serr := goleanShimStrconvParseUint(s, base, bitSize)
	if wv != sv || (werr == nil) != (serr == nil) {
		return fmt.Sprintf("value/err-nil: %q base=%d bits=%d want (%d,%v) got (%d,%v)", s, base, bitSize, wv, werr, sv, serr)
	}
	if werr == nil {
		return ""
	}
	if werr.Error() != serr.Error() {
		return fmt.Sprintf("text: %q base=%d bits=%d want %q got %q", s, base, bitSize, werr.Error(), serr.Error())
	}
	wn, wok := werr.(*strconv.NumError)
	sn, sok := serr.(*strconv.NumError)
	if !wok || !sok || wn.Func != sn.Func || wn.Num != sn.Num || wn.Err != sn.Err {
		return fmt.Sprintf("numerror: %q base=%d bits=%d want %#v got %#v", s, base, bitSize, werr, serr)
	}
	if errors.Is(werr, strconv.ErrSyntax) != errors.Is(serr, strconv.ErrSyntax) || errors.Is(werr, strconv.ErrRange) != errors.Is(serr, strconv.ErrRange) {
		return fmt.Sprintf("sentinel: %q base=%d bits=%d", s, base, bitSize)
	}
	return ""
}
func main() {
	n, _ := strconv.Atoi(os.Args[1]); seed, _ := strconv.ParseInt(os.Args[2], 10, 64)
	rng := rand.New(rand.NewSource(seed))
	alphabet := []byte("0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_-+ .xX\"\\\t\xff\xc3\xa9")
	extremes := []string{"", "0", "18446744073709551615", "18446744073709551616", "99999999999999999999999", "zzzzzzzzzzzzz", "1111111111111111111111111111111111111111111111111111111111111111", "11111111111111111111111111111111111111111111111111111111111111111", "0x1f", "0b1", "0o7", "1_000", "+1", "-1"}
	mismatches, errs, oks := 0, 0, 0
	for i := 0; i < n; i++ {
		var s string
		if i%10 == 0 { s = extremes[rng.Intn(len(extremes))] } else {
			l := rng.Intn(24); b := make([]byte, l)
			for k := range b { b[k] = alphabet[rng.Intn(len(alphabet))] }
			s = string(b)
		}
		base := 2 + rng.Intn(35)
		if rng.Intn(20) == 0 { base = 0 } // recorded bound: the shim refuses (counted)
		bits := []int{0, 8, 16, 32, 64, 3, 7, 63, 65}[rng.Intn(9)]
		before := refused
		if m := trial(s, base, bits); m != "" { mismatches++; if mismatches <= 20 { fmt.Println("MISMATCH", m) } }
		if refused == before { if _, err := strconv.ParseUint(s, base, bits); err != nil { errs++ } else { oks++ } }
	}
	fmt.Printf("trials=%d ok-path=%d error-path=%d refused(recorded bounds: base 0 / bitSize>64)=%d mismatches=%d\n", n, oks, errs, refused, mismatches)
	if mismatches > 0 { os.Exit(1) }
}
HARNESS
} > "$OUT/main.go"
cd "$OUT" && GO111MODULE=off GOCACHE="$ROOT/artifacts/go-build-cache" go run main.go "$N" "$SEED"
