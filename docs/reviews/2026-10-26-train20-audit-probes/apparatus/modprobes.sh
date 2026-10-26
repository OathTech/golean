#!/usr/bin/env bash
# modprobes.sh — gc go1.26.5 (module mode, the environment scripts/coverage-negative's module
# leg uses, minus GOWORK=off unless a case sets it) vs the frontend over go.work/GOWORK shapes
# and go.mod toolchain/lexical shapes. Output: TSV  case | gc rc | gc first line | fe rc | fe
# first line. The frontend binary: $GOLEAN_FRONTEND, else <root>/.tmp/nativefrontend
# (`GO111MODULE=off go build -o .tmp/nativefrontend ./tools/nativefrontend`). Scratch under
# <root>/.tmp/probes/ (gitignored). The measured table of 2026-10-26 is modprobes.tsv beside.
set -u
ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"
FE="${GOLEAN_FRONTEND:-$ROOT/.tmp/nativefrontend}"
[[ -x "$FE" ]] || { echo "modprobes: no frontend at $FE (build it, or set GOLEAN_FRONTEND)" >&2; exit 2; }
P="$ROOT/.tmp/probes/cases"
rm -rf "$P"; mkdir -p "$P"
GOCACHE_DIR="$ROOT/.tmp/probes/gocache"; mkdir -p "$GOCACHE_DIR"
PROBE=$'package main\n\nfunc probe() (r bool) {\n\tdefer func() { r = recover() == nil }()\n\tpanic(nil)\n}\n\nfunc main() { println(probe()) }\n'
GOMOD=$'module test\ngo 1.26\n'

mk() { local d="$P/$1"; mkdir -p "$d"; printf '%s' "$PROBE" > "$d/main.go"; printf '%s' "$GOMOD" > "$d/go.mod"; printf '%s' "$d"; }
trim() { printf '%s' "$1" | head -1 | cut -c1-150; }
gc() { local d="$1"; shift; (cd "$d" && env -u GOWORK -u GOENV GO111MODULE=on GOFLAGS= GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local GOCACHE="$GOCACHE_DIR" "$@" go run . 2>&1); }
fe() { local d="$1"; shift; (cd "$P" && env -u GOWORK -u GOENV "$@" "$FE" --dir "$d" --out "$d/wire.json" 2>&1); }
row() { local label="$1" d="$2"; shift 2; local g grc f frc
  g="$(gc "$d" "$@")"; grc=$?; f="$(fe "$d" "$@")"; frc=$?
  [[ -f "$d/wire.json" ]] && f="${f:-(wire written)}"
  printf '%s\t%s\t%s\t%s\t%s\n' "$label" "$grc" "$(trim "$g")" "$frc" "$(trim "${f#nativefrontend: native frontend unsupported: }")"; }
printf 'case\tgc_rc\tgc_first_line\tfe_rc\tfe_first_line\n'

# ── go.work / GOWORK / the env file / GOFLAGS ──────────────────────────────
d=$(mk w01-control);                                                                row "w01 control: go.mod only" "$d"
d=$(mk w02-gowork-beside); printf 'go 1.26\nuse .\n' > "$d/go.work";               row "w02 go.work beside (go 1.26, use .)" "$d"
d=$(mk w03-gowork-godebug); printf 'go 1.26\nuse .\ngodebug panicnil=1\n' > "$d/go.work"; row "w03 go.work beside + godebug panicnil=1" "$d"
d=$(mk w04-auto-none);                                                              row "w04 GOWORK=auto, no go.work" "$d" GOWORK=auto
d=$(mk w05-auto-beside); printf 'go 1.26\nuse .\ngodebug panicnil=1\n' > "$d/go.work"; row "w05 GOWORK=auto, go.work beside" "$d" GOWORK=auto
d=$(mk w06-syntax); printf 'go 1.26\nuse\nfrobnicate\n' > "$d/go.work";             row "w06 go.work beside with syntax errors" "$d"
d=$(mk w07-use-missing); printf 'go 1.26\nuse ./nonexistent\n' > "$d/go.work";      row "w07 go.work beside, use ./nonexistent only" "$d"
mkdir -p "$P/w08/m"; printf '%s' "$PROBE" > "$P/w08/m/main.go"; printf '%s' "$GOMOD" > "$P/w08/m/go.mod"; printf 'go 1.26\nuse ./m\n' > "$P/w08/go.work"
                                                                                    row "w08 parent go.work use ./m, module in m/" "$P/w08/m"
mkdir -p "$P/w09/m" "$P/w09/other"; printf '%s' "$PROBE" > "$P/w09/m/main.go"; printf '%s' "$GOMOD" > "$P/w09/m/go.mod"; printf 'module other\ngo 1.26\n' > "$P/w09/other/go.mod"; printf 'package other\n' > "$P/w09/other/o.go"; printf 'go 1.26\nuse ./other\n' > "$P/w09/go.work"
                                                                                    row "w09 parent go.work uses ./other, not this module" "$P/w09/m"
mkdir -p "$P/w10/real/ws/m" "$P/w10/linkdir"; printf '%s' "$PROBE" > "$P/w10/real/ws/m/main.go"; printf '%s' "$GOMOD" > "$P/w10/real/ws/m/go.mod"; printf 'go 1.26\nuse ./m\ngodebug panicnil=1\n' > "$P/w10/real/ws/go.work"; ln -s ../real/ws/m "$P/w10/linkdir/mlink"
                                                                                    row "w10 symlink INTO a workspace (logical path has no go.work; physical does)" "$P/w10/linkdir/mlink"
mkdir -p "$P/w11/real2/m" "$P/w11/ws2"; printf '%s' "$PROBE" > "$P/w11/real2/m/main.go"; printf '%s' "$GOMOD" > "$P/w11/real2/m/go.mod"; printf 'go 1.26\nuse ./mlink\ngodebug panicnil=1\n' > "$P/w11/ws2/go.work"; ln -s ../real2/m "$P/w11/ws2/mlink"
                                                                                    row "w11 symlink FROM a workspace dir (logical path has go.work; physical does not)" "$P/w11/ws2/mlink"
d=$(mk w12-goenv-off); printf 'go 1.26\nuse .\ngodebug panicnil=1\n' > "$d/go.work"; printf 'GOWORK=off\n' > "$d/goenv"
                                                                                    row "w12 go.work beside; GOENV file says GOWORK=off; process GOWORK unset" "$d" GOENV="$d/goenv"
d=$(mk w13-goenv-path); mkdir -p "$P/w13-elsewhere"; printf 'go 1.26\nuse %s\ngodebug panicnil=1\n' "$d" > "$P/w13-elsewhere/go.work"; printf 'GOWORK=%s\n' "$P/w13-elsewhere/go.work" > "$d/goenv"
                                                                                    row "w13 NO go.work in the walk; GOENV file names a go.work elsewhere (godebug panicnil=1)" "$d" GOENV="$d/goenv"
d=$(mk w14-OFF); printf 'go 1.26\nuse .\n' > "$d/go.work";                          row "w14 GOWORK=OFF (uppercase), go.work beside" "$d" GOWORK=OFF
d=$(mk w15-gopath); printf 'go 1.26\nuse .\ngodebug asynctimerchan=0\n' > "$d/go.work"; row "w15 GO111MODULE=off (GOPATH mode), go.work beside (gc prints true for its OWN reason: GOPATH mode's go1.16 godebug defaults, panicnil=1 — not the go.work; see machine.sh)" "$d" GO111MODULE=off
d=$(mk w16-symlink-file); printf 'go 1.26\nuse .\ngodebug panicnil=1\n' > "$P/w16-target.work"; ln -s ../w16-target.work "$d/go.work"
                                                                                    row "w16 go.work is a symlink to a regular file" "$d"
d=$(mk w17-dangling); ln -s ../nonexistent.work "$d/go.work";                      row "w17 go.work is a dangling symlink" "$d"
d=$(mk w18-floor); printf 'go 1.26.6\nuse .\n' > "$d/go.work";                      row "w18 go.work beside with go 1.26.6" "$d"
d=$(mk w19-dir); mkdir -p "$P/w19-dir/gw.d";                                        row "w19 GOWORK=<a directory>" "$d" GOWORK="$P/w19-dir/gw.d"
mkdir -p "$P/w20/go.work"; printf '%s' "$PROBE" > "$P/w20/go.work/main.go"; printf '%s' "$GOMOD" > "$P/w20/go.work/go.mod"
                                                                                    row "w20 the lowered directory is itself named go.work" "$P/w20/go.work"
d=$(mk w21-off-beside); printf 'go 1.26\nuse .\ngodebug panicnil=1\n' > "$d/go.work"; row "w21 GOWORK=off, go.work beside with godebug" "$d" GOWORK=off
d=$(mk w22-rel); printf 'go 1.26\nuse .\n' > "$d/go.work";                           row "w22 GOWORK=go.work (relative)" "$d" GOWORK=go.work
d=$(mk w23-nomod-work); rm "$d/go.mod"; printf 'go 1.26\nuse .\n' > "$d/go.work";   row "w23 go.work beside, NO go.mod" "$d"
mkdir -p "$P/w24/m"; printf '%s' "$PROBE" > "$P/w24/m/main.go"; printf 'go 1.26\n' > "$P/w24/go.work"
                                                                                    row "w24 parent go.work (no use), m/ WITHOUT go.mod" "$P/w24/m"
d=$(mk w25-trailing); printf 'go 1.26\nuse .\n' > "$d/go.work";                      row "w25 GOWORK=<abs path>/ (trailing slash)" "$d" GOWORK="$d/go.work/"
d=$(mk w27-modfile-flag); printf 'module test\ngo 1.26\ngodebug panicnil=1\n' > "$d/alt.mod"
                                                                                    row "w27 GOFLAGS=-modfile=alt.mod (alt.mod carries godebug panicnil=1; go.mod clean)" "$d" GOFLAGS=-modfile=alt.mod
d=$(mk w28-goenv-modfile); printf 'module test\ngo 1.26\ngodebug panicnil=1\n' > "$d/alt.mod"; printf 'GOFLAGS=-modfile=alt.mod\n' > "$d/goenv"
                                                                                    row "w28 GOENV file says GOFLAGS=-modfile=alt.mod; process GOFLAGS unset" "$d" GOENV="$d/goenv"

# ── go.mod toolchain / lexical shapes (no go.work anywhere) ────────────────
t() { local name="$1" mod="$2" label="$3"; local d; d=$(mk "$name"); printf '%s' "$mod" > "$d/go.mod"; row "$label" "$d"; }
t t01 $'module test\ngo 1.26.5\ntoolchain go1.26.5\n'                "t01 go 1.26.5 + toolchain go1.26.5 (textually equal)"
t t02 $'module test\ngo 1.26\ntoolchain go1.26.5\n'                  "t02 go 1.26 + toolchain go1.26.5"
t t03 $'module test\ngo 1.26.0\ntoolchain go1.26.5\n'                "t03 go 1.26.0 + toolchain go1.26.5"
t t04 $'module test\ngo 1.27\ntoolchain go1.26.5\n'                  "t04 go 1.27 + toolchain go1.26.5"
t t05 $'module test\ngo 1.26\ntoolchain default\n'                   "t05 go 1.26 + toolchain default"
t t06 $'module test\ntoolchain go1.26.5\ngo 1.26\n'                  "t06 toolchain line BEFORE the go line"
t t07 $'module test\ngo 1.26\ntoolchain go1.26.5\ntoolchain go1.26.5\n' "t07 two toolchain lines"
t t08 $'module test\ngo 1.26\ntoolchain    go1.26.5    // pinned\n'  "t08 extra spaces + trailing comment"
t t09 $'module test\ngo 1.26\ntoolchain\tgo1.26.5\n'                 "t09 tab between toolchain and name"
t t10 $'module test\r\ngo 1.26\r\ntoolchain go1.26.5\r\n'            "t10 CRLF line endings"
t t11 $'module\xc2\xa0test\ngo 1.26\n'                               "t11 NBSP (U+00A0) between module and path"
t t12 $'module test\ngo\xc2\xa01.26\n'                               "t12 NBSP between go and version"
t t13 $'module test\ngo 1.26\ntoolchain go1.26.5 extra\n'            "t13 toolchain go1.26.5 extra"
t t14 $'module test\ngo 1.26\ntoolchain go1.26.5-custom\n'           "t14 toolchain go1.26.5-custom (a named toolchain)"
t t15 $'module test\ngo 1.26\ntoolchain go1.26.5.1\n'                "t15 toolchain go1.26.5.1"
t t16 $'module test\ngo 1.26\ntoolchain go1\n'                       "t16 toolchain go1"
t t17 $'module test\ngo 1.26\nrequire a.b/c v2.0.0\n'                "t17 require a.b/c v2.0.0 (major mismatch)"
t t18 $'module test\ngo 1.26\nrequire a.b/c/v2 v1.0.0\n'             "t18 require a.b/c/v2 v1.0.0 (major mismatch)"
t t19 $'module test\ngo 1.26\ntoolchain go1.26.5\ngo 1.26\n'         "t19 duplicate go line"
t t20 $'module test\ntoolchain go1.26.5\n'                           "t20 toolchain line, NO go line (gc: the go 1.16 language, panicnil=1 — prints true)"
t t21 $'module test\ngo 1.26 // lang\ntoolchain go1.26.5 //pin\n'    "t21 comments on both lines"
t t22 $'module test\ngo 1.26\ntoolchain go1.26.5\nrequire ()\n'      "t22 require () one-line empty block"
t t23 $'module test\ngo 1.26\nrequire (\n)\n'                        "t23 require ( newline )"
t t24 $'module test\ngo 1.26\nrequire ( // c\n)\n'                   "t24 require ( // c newline )"
t t25 $'\xef\xbb\xbfmodule test\ngo 1.26\n'                          "t25 UTF-8 BOM before module"
t t26 $'module test\ngo 1.26\ntool foo{bar\n'                        "t26 tool foo{bar (brace in a tool path)"
t t27 $'module test\ngo 1.26\nreplace a.b/c => ./x{y\n'              "t27 replace target ./x{y"
t t28 $'module test\x0bgo 1.26\n'                                    "t28 vertical tab between module test and go 1.26 (one line)"
t t29 $'module\x0ctest\ngo 1.26\n'                                   "t29 form feed between module and path"
t t30 $'module test\ngo 1.26\ntoolchain go1.26.5\ngodebug ()\n'      "t30 godebug () with the pin"
t t31 $'module test\ngo 1.26\nrequire a.b/c v1.0.0 // indirect\n'    "t31 require with // indirect"
t t32 $'module test\ngo 1.26\nrequire a.b/c v1.0.0+incompatible\n'   "t32 +incompatible on a v1"
t t33 $'module test\ngo 1.26\nrequire a.b/c/v2 v2.0.0+incompatible\n' "t33 +incompatible on a /v2 path"
t t34 $'module test\ngo 1.26\nrequire A.b/c v1.0.0\n'                "t34 uppercase in a module path"
t t35 $'module test\ngo 1.26\nrequire a.b/c v1.0.0-rc.1\n'           "t35 prerelease require version"
t t36 $'module test\ngo 1.26\nrequire a.b/c v1.0.0+build.1\n'        "t36 build metadata on a require version"
t t37 $'module test\ngo 1.26\nignore ./a\xe2\x80\xa8b\n'             "t37 U+2028 line separator inside an ignore path"
t t38 $'module test\ngo 1.26\ntoolchain go1.26.5 \n'                 "t38 trailing space after the toolchain name"
t t39 $'module test\ngo 1.26\ntoolchain GO1.26.5\n'                  "t39 toolchain GO1.26.5 (uppercase)"
t t40 $'module test\ngo 1.26\ntoolchain go1.26.5rc1\n'               "t40 toolchain go1.26.5rc1"
