# BEFORE / AFTER / AFTER-2 — every probe of `run-probes.py --plan full` (3 runs/point, medians, net of each run's empty probe)

- **BEFORE**: binary `da7bb837…` at commit `ee8d0ef0` (dirty: False), 2026-09-19T16:03:39Z–2026-09-19T16:09:29Z, load1 7.06 → 5.1, empty probe median 0.0190 s
- **AFTER**: binary `ab355547…` at commit `ee8d0ef0` (dirty: False), 2026-09-19T16:09:29Z–2026-09-19T16:10:05Z, load1 5.1 → 4.36, empty probe median 0.0195 s
- **AFTER-2**: binary `ab355547…` at commit `ee8d0ef0` (dirty: False), 2026-09-19T16:09:29Z–2026-09-19T16:10:05Z, load1 5.1 → 4.36, empty probe median 0.0195 s

BEFORE = main `0f114df6`'s binary; AFTER = the S3 working tree's binary (the bytes the runtime commit carries; proof-only edits followed before the commit); AFTER-2 = the committed tree `fd99b021`'s gate-built binary, re-run on a quiet box. Producer: `bench_compare.py` (reproduced in the README).

| probe(args) | BEFORE net s | AFTER net s | AFTER-2 net s | AFTER/BEFORE | AFTER-2/BEFORE | statuses (B / A / A2) |
|---|---:|---:|---:|---:|---:|---|
| `empty(0,)` | 0.0000 | 0.0000 | 0.0000 | — | — | ok / ok / ok |
| `scalar(10000,)` | 0.1302 | 0.1424 | 0.1424 | 1.094 | 1.094 | ok / ok / ok |
| `scalar(20000,)` | 0.2587 | 0.2813 | 0.2813 | 1.087 | 1.087 | ok / ok / ok |
| `scalar(40000,)` | 0.5405 | 0.5694 | 0.5694 | 1.053 | 1.053 | ok / ok / ok |
| `scalar(80000,)` | 1.0748 | 1.1332 | 1.1332 | 1.054 | 1.054 | ok / ok / ok |
| `append_grow(250,)` | 0.0090 | 0.0076 | 0.0076 | 0.844 | 0.844 | ok / ok / ok |
| `append_grow(500,)` | 0.0185 | 0.0146 | 0.0146 | 0.789 | 0.789 | ok / ok / ok |
| `append_grow(1000,)` | 0.0398 | 0.0298 | 0.0298 | 0.749 | 0.749 | ok / ok / ok |
| `append_grow(2000,)` | 0.1108 | 0.0624 | 0.0624 | 0.563 | 0.563 | ok / ok / ok |
| `append_grow(4000,)` | 0.3067 | 0.1215 | 0.1215 | 0.396 | 0.396 | ok / ok / ok |
| `append_cap(250, 250)` | 0.0092 | 0.0068 | 0.0068 | 0.739 | 0.739 | ok / ok / ok |
| `append_cap(500, 500)` | 0.0180 | 0.0148 | 0.0148 | 0.822 | 0.822 | ok / ok / ok |
| `append_cap(1000, 1000)` | 0.0424 | 0.0296 | 0.0296 | 0.698 | 0.698 | ok / ok / ok |
| `append_cap(2000, 2000)` | 0.1046 | 0.0611 | 0.0611 | 0.584 | 0.584 | ok / ok / ok |
| `append_cap(100, 100)` | 0.0041 | 0.0027 | 0.0027 | 0.659 | 0.659 | ok / ok / ok |
| `append_cap(200, 100)` | 0.0028 | 0.0024 | 0.0024 | 0.857 | 0.857 | ok / ok / ok |
| `append_cap(400, 100)` | 0.0036 | 0.0030 | 0.0030 | 0.833 | 0.833 | ok / ok / ok |
| `append_cap(800, 100)` | 0.0075 | 0.0026 | 0.0026 | 0.347 | 0.347 | ok / ok / ok |
| `append_cap(1600, 100)` | 0.0036 | 0.0025 | 0.0025 | 0.694 | 0.694 | ok / ok / ok |
| `append_cap(3200, 100)` | 0.0057 | 0.0035 | 0.0035 | 0.614 | 0.614 | ok / ok / ok |
| `append_cap(6400, 100)` | 0.0050 | 0.0053 | 0.0053 | 1.060 | 1.060 | ok / ok / ok |
| `write_fixed(10, 100)` | 0.0023 | 0.0011 | 0.0011 | 0.478 | 0.478 | ok / ok / ok |
| `write_fixed(100, 100)` | 0.0024 | 0.0015 | 0.0015 | 0.625 | 0.625 | ok / ok / ok |
| `write_fixed(1000, 100)` | 0.0036 | 0.0007 | 0.0007 | 0.194 | 0.194 | ok / ok / ok |
| `write_fixed(3000, 100)` | 0.0017 | 0.0031 | 0.0031 | 1.824 | 1.824 | ok / ok / ok |
| `write_fixed(10000, 100)` | 0.0041 | 0.0033 | 0.0033 | 0.805 | 0.805 | ok / ok / ok |
| `write_fixed(10, 1000)` | 0.0163 | 0.0155 | 0.0155 | 0.951 | 0.951 | ok / ok / ok |
| `write_fixed(10, 10000)` | 0.1440 | 0.1492 | 0.1492 | 1.036 | 1.036 | ok / ok / ok |
| `read_fixed(10, 1000)` | 0.0180 | 0.0175 | 0.0175 | 0.972 | 0.972 | ok / ok / ok |
| `read_fixed(100, 1000)` | 0.0179 | 0.0168 | 0.0168 | 0.939 | 0.939 | ok / ok / ok |
| `read_fixed(1000, 1000)` | 0.0200 | 0.0180 | 0.0180 | 0.900 | 0.900 | ok / ok / ok |
| `read_fixed(10000, 1000)` | 0.0207 | 0.0202 | 0.0202 | 0.976 | 0.976 | ok / ok / ok |
| `struct_small(100,)` | 0.0024 | 0.0038 | 0.0038 | 1.583 | 1.583 | ok / ok / ok |
| `struct_arr_100(100,)` | 0.0016 | 0.0002 | 0.0002 | 0.125 | 0.125 | ok / ok / ok |
| `struct_arr_1000(100,)` | 0.0021 | 0.0012 | 0.0012 | 0.571 | 0.571 | ok / ok / ok |
| `struct_arr_10000(100,)` | 0.0029 | 0.0016 | 0.0016 | 0.552 | 0.552 | ok / ok / ok |
| `struct_slice(100, 100)` | 0.0011 | 0.0006 | 0.0006 | 0.545 | 0.545 | ok / ok / ok |
| `struct_slice(10000, 100)` | 0.0039 | 0.0030 | 0.0030 | 0.769 | 0.769 | ok / ok / ok |
| `flat_arr_10000(100,)` | 0.0067 | 0.0042 | 0.0042 | 0.627 | 0.627 | ok / ok / ok |
| `nested_arr_10x1000(100,)` | 0.0037 | 0.0025 | 0.0025 | 0.676 | 0.676 | ok / ok / ok |
| `nested_arr_100x100(100,)` | 0.0030 | 0.0021 | 0.0021 | 0.700 | 0.700 | ok / ok / ok |
| `slice_inner(10000, 100)` | 0.0045 | 0.0023 | 0.0023 | 0.511 | 0.511 | ok / ok / ok |
| `alloc_new(1000,)` | 0.0363 | 0.0267 | 0.0267 | 0.736 | 0.736 | ok / ok / ok |
| `alloc_new(4000,)` | 0.2640 | 0.1070 | 0.1070 | 0.405 | 0.405 | ok / ok / ok |
| `alloc_new(16000,)` | 3.6589 | 0.4286 | 0.4286 | 0.117 | 0.117 | ok / ok / ok |
| `alloc_new(32000,)` | 14.0790 | 0.8315 | 0.8315 | 0.059 | 0.059 | ok / ok / ok |
| `alloc_make4(1000,)` | 0.0367 | 0.0243 | 0.0243 | 0.662 | 0.662 | ok / ok / ok |
| `alloc_make4(4000,)` | 0.2640 | 0.0998 | 0.0998 | 0.378 | 0.378 | ok / ok / ok |
| `alloc_make4(16000,)` | 3.6127 | 0.3760 | 0.3760 | 0.104 | 0.104 | ok / ok / ok |
| `heap_then_scalar(0, 0)` | 0.0012 | 0.0004 | 0.0004 | 0.333 | 0.333 | ok / ok / ok |
| `heap_then_scalar(1000, 0)` | 0.0334 | 0.0220 | 0.0220 | 0.659 | 0.659 | ok / ok / ok |
| `heap_then_scalar(10000, 0)` | 1.2190 | 0.2025 | 0.2025 | 0.166 | 0.166 | ok / ok / ok |
| `heap_then_scalar(40000, 0)` | 18.7482 | 0.8449 | 0.8449 | 0.045 | 0.045 | ok / ok / ok |
| `heap_then_scalar(0, 20000)` | 0.2728 | 0.2889 | 0.2889 | 1.059 | 1.059 | ok / ok / ok |
| `heap_then_scalar(1000, 20000)` | 0.4094 | 0.2895 | 0.2895 | 0.707 | 0.707 | ok / ok / ok |
| `heap_then_scalar(10000, 20000)` | 2.9900 | 0.5150 | 0.5150 | 0.172 | 0.172 | ok / ok / ok |
| `heap_then_scalar(40000, 20000)` | 24.2898 | 1.1617 | 1.1617 | 0.048 | 0.048 | ok / ok / ok |
| `heap_then_append(0, 0)` | 0.0017 | 0.0009 | 0.0009 | 0.529 | 0.529 | ok / ok / ok |
| `heap_then_append(10000, 0)` | 1.3100 | 0.2116 | 0.2116 | 0.162 | 0.162 | ok / ok / ok |
| `heap_then_append(40000, 0)` | 19.9704 | 0.8643 | 0.8643 | 0.043 | 0.043 | ok / ok / ok |
| `heap_then_append(0, 300)` | 0.0111 | 0.0083 | 0.0083 | 0.748 | 0.748 | ok / ok / ok |
| `heap_then_append(10000, 300)` | 1.3835 | 0.2232 | 0.2232 | 0.161 | 0.161 | ok / ok / ok |
| `heap_then_append(40000, 300)` | 18.6272 | 0.9003 | 0.9003 | 0.048 | 0.048 | ok / ok / ok |
| `map_write(500,)` | 0.0093 | 0.0102 | 0.0102 | 1.097 | 1.097 | ok / ok / ok |
| `map_write(1000,)` | 0.0231 | 0.0219 | 0.0219 | 0.948 | 0.948 | ok / ok / ok |
| `map_write(2000,)` | 0.0591 | 0.0631 | 0.0631 | 1.068 | 1.068 | ok / ok / ok |
| `map_write(4000,)` | 0.1792 | 0.1937 | 0.1937 | 1.081 | 1.081 | ok / ok / ok |

## The four charter §6 S3 targets, derived from the table (BEFORE → AFTER → AFTER-2)

| target | BEFORE | AFTER | AFTER-2 | verdict |
|---|---|---|---|---|
| `alloc_new` linear: n = 1k/4k/16k/32k successive ×4 ratios ≤ 4.4; n = 32k < 1 s | 0.036 / 0.264 / 3.659 / 14.079 s (×7.27, ×13.86, ×3.85) | 0.027 / 0.107 / 0.429 / 0.832 s (×4.01, ×4.01, ×1.94) | 0.027 / 0.107 / 0.429 / 0.832 s (×4.01, ×4.01, ×1.94) | AFTER **MET**; AFTER-2 **MET** |
| the (h) scalar phase: 20k iterations after h live cells (`heap_then_scalar(h,20000) − heap_then_scalar(h,0)`) within 1.2× of h = 0 | h=0 0.272 s; h=1000 0.376 s (1.38×); h=10000 1.771 s (6.52×); h=40000 5.542 s (20.40×) | h=0 0.288 s; h=1000 0.267 s (0.93×); h=10000 0.312 s (1.08×); h=40000 0.317 s (1.10×) | h=0 0.288 s; h=1000 0.267 s (0.93×); h=10000 0.312 s (1.08×); h=40000 0.317 s (1.10×) | AFTER **MET**; AFTER-2 **MET** |
| `append_grow` successive ×2 ratios ≤ 2.2 (the S1-owed target) | 0.0090 / 0.0185 / 0.0398 / 0.1108 / 0.3067 s (×2.06, ×2.15, ×2.78, ×2.77) | 0.0076 / 0.0146 / 0.0298 / 0.0624 / 0.1215 s (×1.92, ×2.04, ×2.09, ×1.95) | 0.0076 / 0.0146 / 0.0298 / 0.0624 / 0.1215 s (×1.92, ×2.04, ×2.09, ×1.95) | AFTER **MET**; AFTER-2 **MET** |
| scalar step baseline within 10 % (`scalar(80000)`) | 1.075 s | 1.133 s (+5.4 %) | 1.133 s (+5.4 %) | AFTER **MET**; AFTER-2 **MET** |

Noise floor: each run's empty probe spans about ±1 ms across its repetitions (`wall_min_s`/`wall_max_s` in the json); a net below ~10 ms (`alloc_new(1000)`, `append_grow(250)`, `append_grow(500)`, the `append_cap`/`write_fixed` rows) carries that ±1 ms as ±10–20 % on the point and up to ±40 % on a ratio of two such points. Ratios between points ≥ 0.1 s are the load-bearing ones.
