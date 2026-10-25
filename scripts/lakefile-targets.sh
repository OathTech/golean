# Shared lakefile.toml target parser — SOURCED by scripts/ci (the build-by-name list and the
# default-target split check) and scripts/check-lake-check (the modules `lake check` imports, for
# its coverage count). Moved out of scripts/ci unchanged by lane gate/contract-pins-1025
# (2026-10-25) so the two cannot drift: one canonical parser, as scripts/lean-scan.sh is for the
# Lean-source scans. Call from the checkout root.
#
# lakefile_targets: one line per declared target — `lib <name> <module>...`
# (a library's modules are its `globs`, each an exact module name; a library
# without `globs` is listed with no modules and enumerated below as its root
# module plus every module under the root's directory, the walk the kernel
# replay does) or `exe <name> <root>`. Any other key in a target section, a
# glob that is not an exact module name, or a target without a name prints an
# `unsupported` line, as does TOML's other spellings of a target — the
# inline-array form `lean_exe = [{ name = …, root = … }]` and a single
# `[lean_lib]` table — and the build FAILS rather than build a set it cannot
# name (extend the parser, deliberately; review F4, 2026-10-22).
lakefile_targets() {
  awk '
    function flush(   i, n, a) {
      if (kind == "") return
      if (name == "") print "unsupported", kind, "section without a name"
      else if (kind == "lib") print "lib", name, globs
      else if (root == "") print "unsupported exe", name, "without a root"
      else print "exe", name, root
      kind = ""; name = ""; globs = ""; root = ""
    }
    /^\[\[lean_lib\]\]/ { flush(); kind = "lib"; next }
    /^\[\[lean_exe\]\]/ { flush(); kind = "exe"; next }
    /^\[lean_(lib|exe)\]/ { flush(); print "unsupported single-table", $0; next }
    /^\[/ { flush(); next }
    /^[[:space:]]*lean_(lib|exe)[[:space:]]*=/ { flush(); print "unsupported inline-array target", $0; next }
    kind == "" || /^[[:space:]]*(#|$)/ { next }
    /^name = "[A-Za-z0-9_-]+"$/ { name = $0; sub(/^name = "/, "", name); sub(/"$/, "", name); next }
    kind == "exe" && /^root = "[A-Za-z0-9_.]+"$/ { root = $0; sub(/^root = "/, "", root); sub(/"$/, "", root); next }
    kind == "lib" && /^globs = \[.*\]$/ {
      globs = $0; sub(/^globs = \[/, "", globs); sub(/\]$/, "", globs); gsub(/[",]/, " ", globs)
      n = split(globs, a, " ")
      for (i = 1; i <= n; i++) if (a[i] !~ /^[A-Za-z0-9_.]+$/) print "unsupported glob", name ":", a[i]
      if (n == 0) print "unsupported empty globs", name
      next
    }
    { print "unsupported", kind, name ":", $0 }
    END { flush() }
  ' lakefile.toml
}

# The default targets, as a space-separated list (`defaultTargets = [...]`, possibly wrapped).
lakefile_default_targets() {
  tr -d '\n' < lakefile.toml | sed -n 's/.*defaultTargets = \[\([^]]*\)\].*/\1/p' | tr -d '",'
}

# The modules of ONE library, by its `lakefile_targets` line (`lib <name> <module>...`): the
# globs when it has them, else the root module plus every module under the root's directory
# (the walk the kernel replay does). Prints nothing for a library without globs whose root
# module file is missing — the caller fails closed on that.
lakefile_lib_modules() { # <lib line>
  local kind name rest
  read -r kind name rest <<< "$1"
  [ "$kind" = lib ] || return 1
  if [ -n "$rest" ]; then printf '%s\n' $rest
  elif [ -f "$name.lean" ]; then
    printf '%s\n' "$name"
    [ -d "$name" ] && find "$name" -name '*.lean' -not -path '*/.lake/*' | sed 's|\.lean$||; s|/|.|g' | LC_ALL=C sort
  fi
}
