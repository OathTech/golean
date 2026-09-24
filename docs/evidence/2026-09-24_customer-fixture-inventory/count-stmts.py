#!/usr/bin/env python3
"""[AGENT] Recursive statement-node census over a retained nativefrontend wire.

A STATEMENT NODE is any JSON object carrying a string "stmt" key (the wire's
statement tag; `stmtAllowedKeys`, GoLean/NativeToIR.lean ~line 170). The walk
descends the WHOLE document (every object value, every array element), so
statements nested in `then`/`else`/`body`/function bodies/`unseq` completions
are all counted -- not a grep over the top level.

Emitted per wire (TSV to stdout, one `unit` per file):
  total statements, `"stmt":"unseq"` graph nodes, per-graph-body-kind
  occurrence counts (`occs[].kind`: eval/invoke/target/load/guard/recv/
  allocate/wide), legacy probe statements (`"stmt":"unseq-probe"`), and the
  full statement-tag histogram.
"""
import json, pathlib, sys
from collections import Counter

OCC_KINDS = ['eval', 'invoke', 'target', 'load', 'guard', 'recv', 'allocate', 'wide']


def walk(node, stmts, occs):
    if isinstance(node, dict):
        tag = node.get('stmt')
        if isinstance(tag, str):
            stmts[tag] += 1
            if tag == 'unseq':
                for o in node.get('occs') or []:
                    if isinstance(o, dict):
                        occs[str(o.get('kind'))] += 1
        for v in node.values():
            walk(v, stmts, occs)
    elif isinstance(node, list):
        for v in node:
            walk(v, stmts, occs)


def main(paths):
    cols = ['unit', 'total_stmts', 'unseq_nodes', 'legacy_unseq_probe'] + \
           ['occ_' + k for k in OCC_KINDS] + ['occ_other', 'stmt_histogram']
    print('\t'.join(cols))
    for p in sorted(pathlib.Path(x) for x in paths):
        stmts, occs = Counter(), Counter()
        walk(json.loads(p.read_text()), stmts, occs)
        hist = ' '.join(f'{k}={v}' for k, v in sorted(stmts.items()))
        other = sum(v for k, v in occs.items() if k not in OCC_KINDS)
        print('\t'.join([p.stem, str(sum(stmts.values())), str(stmts['unseq']),
                         str(stmts['unseq-probe'])] +
                        [str(occs[k]) for k in OCC_KINDS] + [str(other), hist]))


if __name__ == '__main__':
    main(sys.argv[1:])
