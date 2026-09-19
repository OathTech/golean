# BEFORE / AFTER / AFTER-2 — every probe of `run-probes.py --plan full` (3 runs/point, medians, net of each run's empty probe)

- **BEFORE**: binary `da7bb837…` at commit `0f114df6` (dirty: False), 2026-09-19T05:23:21Z–2026-09-19T05:29:02Z, load1 3.9 → 2.16, empty probe median 0.0185 s
- **AFTER**: binary `12ebb0e1…` at commit `0f114df6` (dirty: True), 2026-09-19T06:37:17Z–2026-09-19T06:37:51Z, load1 1.86 → 2.31, empty probe median 0.0191 s
- **AFTER-2**: binary `ab355547…` at commit `fd99b021` (dirty: False), 2026-09-19T07:21:56Z–2026-09-19T07:22:31Z, load1 0.97 → 0.99, empty probe median 0.0201 s

BEFORE = main `0f114df6`'s binary; AFTER = the S3 working tree's binary (the bytes the runtime commit carries; proof-only edits followed before the commit); AFTER-2 = the committed tree `fd99b021`'s gate-built binary, re-run on a quiet box. Producer: `bench_compare.py` (reproduced in the README).

| probe(args) | BEFORE net s | AFTER net s | AFTER-2 net s | AFTER/BEFORE | AFTER-2/BEFORE | statuses (B / A / A2) |
|---|---:|---:|---:|---:|---:|---|
| `empty(0,)` | 0.0000 | 0.0000 | 0.0000 | — | — | ok / ok / ok |
| `scalar(10000,)` | 0.1333 | 0.1435 | 0.1503 | 1.077 | 1.128 | ok / ok / ok |
| `scalar(20000,)` | 0.2821 | 0.2800 | 0.2554 | 0.993 | 0.905 | ok / ok / ok |
| `scalar(40000,)` | 0.5214 | 0.5418 | 0.5227 | 1.039 | 1.002 | ok / ok / ok |
| `scalar(80000,)` | 1.0954 | 1.0574 | 1.0359 | 0.965 | 0.946 | ok / ok / ok |
| `append_grow(250,)` | 0.0095 | 0.0085 | 0.0059 | 0.895 | 0.621 | ok / ok / ok |
| `append_grow(500,)` | 0.0191 | 0.0164 | 0.0135 | 0.859 | 0.707 | ok / ok / ok |
| `append_grow(1000,)` | 0.0404 | 0.0332 | 0.0276 | 0.822 | 0.683 | ok / ok / ok |
| `append_grow(2000,)` | 0.1008 | 0.0612 | 0.0599 | 0.607 | 0.594 | ok / ok / ok |
| `append_grow(4000,)` | 0.2961 | 0.1204 | 0.1182 | 0.407 | 0.399 | ok / ok / ok |
| `append_cap(250, 250)` | 0.0090 | 0.0069 | 0.0065 | 0.767 | 0.722 | ok / ok / ok |
| `append_cap(500, 500)` | 0.0193 | 0.0160 | 0.0132 | 0.829 | 0.684 | ok / ok / ok |
| `append_cap(1000, 1000)` | 0.0422 | 0.0307 | 0.0273 | 0.727 | 0.647 | ok / ok / ok |
| `append_cap(2000, 2000)` | 0.1021 | 0.0593 | 0.0613 | 0.581 | 0.600 | ok / ok / ok |
| `append_cap(100, 100)` | 0.0047 | 0.0036 | 0.0028 | 0.766 | 0.596 | ok / ok / ok |
| `append_cap(200, 100)` | 0.0044 | 0.0025 | 0.0023 | 0.568 | 0.523 | ok / ok / ok |
| `append_cap(400, 100)` | 0.0042 | 0.0037 | 0.0018 | 0.881 | 0.429 | ok / ok / ok |
| `append_cap(800, 100)` | 0.0050 | 0.0028 | 0.0017 | 0.560 | 0.340 | ok / ok / ok |
| `append_cap(1600, 100)` | 0.0042 | 0.0044 | 0.0021 | 1.048 | 0.500 | ok / ok / ok |
| `append_cap(3200, 100)` | 0.0058 | 0.0044 | 0.0027 | 0.759 | 0.466 | ok / ok / ok |
| `append_cap(6400, 100)` | 0.0060 | 0.0041 | 0.0038 | 0.683 | 0.633 | ok / ok / ok |
| `write_fixed(10, 100)` | 0.0026 | 0.0021 | 0.0006 | 0.808 | 0.231 | ok / ok / ok |
| `write_fixed(100, 100)` | 0.0021 | 0.0033 | 0.0008 | 1.571 | 0.381 | ok / ok / ok |
| `write_fixed(1000, 100)` | 0.0032 | 0.0034 | 0.0009 | 1.062 | 0.281 | ok / ok / ok |
| `write_fixed(3000, 100)` | 0.0040 | 0.0032 | 0.0014 | 0.800 | 0.350 | ok / ok / ok |
| `write_fixed(10000, 100)` | 0.0058 | 0.0043 | 0.0035 | 0.741 | 0.603 | ok / ok / ok |
| `write_fixed(10, 1000)` | 0.0154 | 0.0158 | 0.0137 | 1.026 | 0.890 | ok / ok / ok |
| `write_fixed(10, 10000)` | 0.1460 | 0.1513 | 0.1450 | 1.036 | 0.993 | ok / ok / ok |
| `read_fixed(10, 1000)` | 0.0171 | 0.0177 | 0.0163 | 1.035 | 0.953 | ok / ok / ok |
| `read_fixed(100, 1000)` | 0.0172 | 0.0175 | 0.0164 | 1.017 | 0.953 | ok / ok / ok |
| `read_fixed(1000, 1000)` | 0.0176 | 0.0179 | 0.0163 | 1.017 | 0.926 | ok / ok / ok |
| `read_fixed(10000, 1000)` | 0.0173 | 0.0172 | 0.0169 | 0.994 | 0.977 | ok / ok / ok |
| `struct_small(100,)` | 0.0026 | 0.0011 | 0.0005 | 0.423 | 0.192 | ok / ok / ok |
| `struct_arr_100(100,)` | 0.0017 | 0.0019 | 0.0003 | 1.118 | 0.176 | ok / ok / ok |
| `struct_arr_1000(100,)` | 0.0027 | 0.0033 | 0.0012 | 1.222 | 0.444 | ok / ok / ok |
| `struct_arr_10000(100,)` | 0.0043 | 0.0041 | 0.0022 | 0.953 | 0.512 | ok / ok / ok |
| `struct_slice(100, 100)` | 0.0025 | 0.0030 | 0.0005 | 1.200 | 0.200 | ok / ok / ok |
| `struct_slice(10000, 100)` | 0.0047 | 0.0037 | 0.0018 | 0.787 | 0.383 | ok / ok / ok |
| `flat_arr_10000(100,)` | 0.0042 | 0.0045 | 0.0031 | 1.071 | 0.738 | ok / ok / ok |
| `nested_arr_10x1000(100,)` | 0.0042 | 0.0024 | 0.0023 | 0.571 | 0.548 | ok / ok / ok |
| `nested_arr_100x100(100,)` | 0.0044 | 0.0021 | 0.0017 | 0.477 | 0.386 | ok / ok / ok |
| `slice_inner(10000, 100)` | 0.0048 | 0.0028 | 0.0029 | 0.583 | 0.604 | ok / ok / ok |
| `alloc_new(1000,)` | 0.0385 | 0.0254 | 0.0254 | 0.660 | 0.660 | ok / ok / ok |
| `alloc_new(4000,)` | 0.2634 | 0.0989 | 0.0966 | 0.375 | 0.367 | ok / ok / ok |
| `alloc_new(16000,)` | 3.6558 | 0.4289 | 0.4340 | 0.117 | 0.119 | ok / ok / ok |
| `alloc_new(32000,)` | 14.1236 | 0.8444 | 0.8652 | 0.060 | 0.061 | ok / ok / ok |
| `alloc_make4(1000,)` | 0.0342 | 0.0260 | 0.0225 | 0.760 | 0.658 | ok / ok / ok |
| `alloc_make4(4000,)` | 0.2488 | 0.1008 | 0.0945 | 0.405 | 0.380 | ok / ok / ok |
| `alloc_make4(16000,)` | 3.4063 | 0.3813 | 0.3655 | 0.112 | 0.107 | ok / ok / ok |
| `heap_then_scalar(0, 0)` | 0.0017 | 0.0032 | -0.0005 | 1.882 | -0.294 | ok / ok / ok |
| `heap_then_scalar(1000, 0)` | 0.0309 | 0.0225 | 0.0201 | 0.728 | 0.650 | ok / ok / ok |
| `heap_then_scalar(10000, 0)` | 1.1805 | 0.2141 | 0.1991 | 0.181 | 0.169 | ok / ok / ok |
| `heap_then_scalar(40000, 0)` | 17.8361 | 0.8494 | 0.8481 | 0.048 | 0.048 | ok / ok / ok |
| `heap_then_scalar(0, 20000)` | 0.2600 | 0.2599 | 0.2825 | 1.000 | 1.087 | ok / ok / ok |
| `heap_then_scalar(1000, 20000)` | 0.4157 | 0.2886 | 0.3056 | 0.694 | 0.735 | ok / ok / ok |
| `heap_then_scalar(10000, 20000)` | 2.9644 | 0.5015 | 0.4691 | 0.169 | 0.158 | ok / ok / ok |
| `heap_then_scalar(40000, 20000)` | 24.6629 | 1.1383 | 1.1118 | 0.046 | 0.045 | ok / ok / ok |
| `heap_then_append(0, 0)` | 0.0014 | 0.0006 | -0.0004 | 0.429 | -0.286 | ok / ok / ok |
| `heap_then_append(10000, 0)` | 1.2820 | 0.2085 | 0.2159 | 0.163 | 0.168 | ok / ok / ok |
| `heap_then_append(40000, 0)` | 18.2339 | 0.8300 | 0.8470 | 0.046 | 0.046 | ok / ok / ok |
| `heap_then_append(0, 300)` | 0.0117 | 0.0086 | 0.0077 | 0.735 | 0.658 | ok / ok / ok |
| `heap_then_append(10000, 300)` | 1.3666 | 0.2181 | 0.2202 | 0.160 | 0.161 | ok / ok / ok |
| `heap_then_append(40000, 300)` | 18.8958 | 0.8203 | 0.8058 | 0.043 | 0.043 | ok / ok / ok |
| `map_write(500,)` | 0.0104 | 0.0099 | 0.0078 | 0.952 | 0.750 | ok / ok / ok |
| `map_write(1000,)` | 0.0225 | 0.0224 | 0.0211 | 0.996 | 0.938 | ok / ok / ok |
| `map_write(2000,)` | 0.0586 | 0.0593 | 0.0600 | 1.012 | 1.024 | ok / ok / ok |
| `map_write(4000,)` | 0.1782 | 0.1887 | 0.1872 | 1.059 | 1.051 | ok / ok / ok |

## The four charter §6 S3 targets, derived from the table (BEFORE → AFTER → AFTER-2)

| target | BEFORE | AFTER | AFTER-2 | verdict |
|---|---|---|---|---|
| `alloc_new` linear: n = 1k/4k/16k/32k successive ×4 ratios ≤ 4.4; n = 32k < 1 s | 0.039 / 0.263 / 3.656 / 14.124 s (×6.84, ×13.88, ×3.86) | 0.025 / 0.099 / 0.429 / 0.844 s (×3.89, ×4.34, ×1.97) | 0.025 / 0.097 / 0.434 / 0.865 s (×3.80, ×4.49, ×1.99) | AFTER **MET**; AFTER-2 **32k < 1 s; ×4 ratios one step 4.49 > 4.4** |
| the (h) scalar phase: 20k iterations after h live cells (`heap_then_scalar(h,20000) − heap_then_scalar(h,0)`) within 1.2× of h = 0 | h=0 0.258 s; h=1000 0.385 s (1.49×); h=10000 1.784 s (6.91×); h=40000 6.827 s (26.43×) | h=0 0.257 s; h=1000 0.266 s (1.04×); h=10000 0.287 s (1.12×); h=40000 0.289 s (1.13×) | h=0 0.283 s; h=1000 0.285 s (1.01×); h=10000 0.270 s (0.95×); h=40000 0.264 s (0.93×) | AFTER **MET**; AFTER-2 **MET** |
| `append_grow` successive ×2 ratios ≤ 2.2 (the S1-owed target) | 0.0095 / 0.0191 / 0.0404 / 0.1008 / 0.2961 s (×2.01, ×2.12, ×2.50, ×2.94) | 0.0085 / 0.0164 / 0.0332 / 0.0612 / 0.1204 s (×1.93, ×2.02, ×1.84, ×1.97) | 0.0059 / 0.0135 / 0.0276 / 0.0599 / 0.1182 s (×2.29, ×2.04, ×2.17, ×1.97) | AFTER **MET**; AFTER-2 **steps 250→500 ×2.29 > 2.2 (the other steps ≤ 2.2)** |
| scalar step baseline within 10 % (`scalar(80000)`) | 1.095 s | 1.057 s (-3.5 %) | 1.036 s (-5.4 %) | AFTER **MET**; AFTER-2 **MET** |

Noise floor: each run's empty probe spans about ±1 ms across its repetitions (`wall_min_s`/`wall_max_s` in the json); a net below ~10 ms (`alloc_new(1000)`, `append_grow(250)`, `append_grow(500)`, the `append_cap`/`write_fixed` rows) carries that ±1 ms as ±10–20 % on the point and up to ±40 % on a ratio of two such points. Ratios between points ≥ 0.1 s are the load-bearing ones.
