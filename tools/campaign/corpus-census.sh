#!/bin/zsh
# Importer-closure census for the validation-corpus split (A4-U25;
# membership corrected at the arc-4 landing fix round, 2026-08-26).
#
# TRACKED at tools/campaign/ since the fix round (F6) — the split's
# stated mechanical check must be re-runnable from a clean clone; the
# old copy lived only in gitignored artifacts/probe/.
#
# What it checks: every corpus module's tracked importers are corpus
# members or the corpus aggregators — i.e. no LIVE module imports a
# corpus module (the fail-closed direction of the split). Membership
# reflects the fix-round correction: the Ring/Round* chains are LIVE
# (witnesses of live laws ship with their laws — see
# proofs/GoLeanProofsCorpus.lean's amended criterion); the corpus is
# exactly the handler-equation validation chains.
cd "$(dirname "$0")/../../proofs" || exit 2
CORPUS="HaeLit HaeEquation StaleLit StaleEquation HhAdvLit HhAdvEquation LaLit LaEquation BlLit BlEquation HaeRejLit HaeRejEquation HhFromLit HhFromEquation SfHbLit SfHbEquation SfPdLit SfPdEquation SCHbLit SCHbEquation SlbLit SlbEquation MsErrEquation MsResite"
AUDIT_CORPUS=""
fail=0
for m in ${=CORPUS}; do
  full="GoLeanProofs.Specs.Raft.$m"
  importers=$(grep -rl "^import $full\$" --include="*.lean" . | grep -v "\.lake")
  for f in ${=importers}; do
    base=$(basename $f .lean)
    dir=$(dirname $f)
    okflag=0
    case " $CORPUS " in *" $base "*) okflag=1;; esac
    case "$f" in ./GoLeanProofsCorpus.lean|./AuditCorpus.lean) okflag=1;; esac
    if [ "$dir" = "./Audit" ]; then case " $AUDIT_CORPUS " in *" $base "*) okflag=1;; esac; fi
    if [ $okflag -eq 0 ]; then echo "VIOLATION: $full imported by $f"; fail=1; fi
  done
done
[ $fail -eq 0 ] && echo "CENSUS CLEAN: all $(echo ${=CORPUS} | wc -w) corpus modules importer-closed (tracked proofs tree)"
exit $fail
