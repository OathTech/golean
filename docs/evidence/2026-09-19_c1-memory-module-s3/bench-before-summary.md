commit 0f114df68e41cc5e40f14274f98af608fd7a5596  golean sha256 da7bb8376164e23f…  go version go1.26.5 linux/amd64  nproc 32  load1 start 3.9 end 2.16  started 2026-09-19T05:23:21Z

empty probe (startup): median 0.0185 s over 7 runs [0.0178..0.0202], rss 72272 KB

steps per loop iteration (fuel bisection): alloc_new=85, append_cap=84, append_grow=84, heap_then_scalar=70, heap_then_scalar=49, map_write=44, read_fixed=55, scalar=49, struct_arr_100=47, write_fixed=51

**(e) scalar loop — per-step baseline** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `scalar(10000,)` | 0.1518 | 0.1507..0.1696 | 0.14 | 0.1333 | 13.33 |
| `scalar(20000,)` | 0.3006 | 0.2987..0.3008 | 0.29 | 0.2821 | 14.10 |
| `scalar(40000,)` | 0.5399 | 0.5381..0.5446 | 0.53 | 0.5214 | 13.04 |
| `scalar(80000,)` | 1.1139 | 1.1052..1.1363 | 1.10 | 1.0954 | 13.69 |

successive net ratios — 10000→20000: ×2.12 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 20000→40000: ×1.85 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 40000→80000: ×2.10 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

per machine step at n=80000: 279 ns (49 steps/iteration)

**(a) the review's loop: `append` growing from nil** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_grow(250,)` | 0.0280 | 0.0276..0.0283 | 0.02 | 0.0095 | 38.00 |
| `append_grow(500,)` | 0.0376 | 0.0374..0.0403 | 0.03 | 0.0191 | 38.20 |
| `append_grow(1000,)` | 0.0589 | 0.0585..0.0593 | 0.05 | 0.0404 | 40.40 |
| `append_grow(2000,)` | 0.1193 | 0.1187..0.1207 | 0.11 | 0.1008 | 50.40 |
| `append_grow(4000,)` | 0.3146 | 0.3142..0.3151 | 0.30 | 0.2961 | 74.02 |

successive net ratios — 250→500: ×2.01 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×2.12 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.50 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×2.94 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f) in-place `append`, w = c (no spill)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(250, 250)` | 0.0275 | 0.0271..0.0291 | 0.02 | 0.0090 | 36.00 |
| `append_cap(500, 500)` | 0.0378 | 0.0370..0.0382 | 0.03 | 0.0193 | 38.60 |
| `append_cap(1000, 1000)` | 0.0607 | 0.0590..0.0609 | 0.05 | 0.0422 | 42.20 |
| `append_cap(2000, 2000)` | 0.1206 | 0.1171..0.1271 | 0.11 | 0.1021 | 51.05 |

successive net ratios — 250→500: ×2.14 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 500→1000: ×2.19 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.42 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(f′) 100 in-place appends, capacity c varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `append_cap(100, 100)` | 0.0232 | 0.0215..0.0241 | 0.01 | 0.0047 | 47.00 |
| `append_cap(200, 100)` | 0.0229 | 0.0214..0.0233 | 0.01 | 0.0044 | 44.00 |
| `append_cap(400, 100)` | 0.0227 | 0.0217..0.0235 | 0.01 | 0.0042 | 42.00 |
| `append_cap(800, 100)` | 0.0235 | 0.0231..0.0241 | 0.01 | 0.0050 | 50.00 |
| `append_cap(1600, 100)` | 0.0227 | 0.0220..0.0237 | 0.01 | 0.0042 | 42.00 |
| `append_cap(3200, 100)` | 0.0243 | 0.0239..0.0244 | 0.02 | 0.0058 | 58.00 |
| `append_cap(6400, 100)` | 0.0245 | 0.0234..0.0251 | 0.02 | 0.0060 | 60.00 |

successive net ratios — 100→200: ×0.94 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 200→400: ×0.95 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 400→800: ×1.19 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 800→1600: ×0.84 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1600→3200: ×1.38 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 3200→6400: ×1.03 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(b) 100 element writes `xs[0] = v`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0211 | 0.0207..0.0221 | 0.01 | 0.0026 | 26.00 |
| `write_fixed(100, 100)` | 0.0206 | 0.0205..0.0209 | 0.01 | 0.0021 | 21.00 |
| `write_fixed(1000, 100)` | 0.0217 | 0.0208..0.0220 | 0.01 | 0.0032 | 32.00 |
| `write_fixed(3000, 100)` | 0.0225 | 0.0219..0.0227 | 0.01 | 0.0040 | 40.00 |
| `write_fixed(10000, 100)` | 0.0243 | 0.0242..0.0243 | 0.01 | 0.0058 | 58.00 |

successive net ratios — 10→100: ×0.81 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×1.52 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→3000: ×1.25 (linear ×3.0, quadratic ×9.0, cubic ×27.0); 3000→10000: ×1.45 (linear ×3.3, quadratic ×11.1, cubic ×37.0)

**(b′) element writes at m = 10, write count varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `write_fixed(10, 100)` | 0.0211 | 0.0207..0.0221 | 0.01 | 0.0026 | 26.00 |
| `write_fixed(10, 1000)` | 0.0339 | 0.0328..0.0346 | 0.03 | 0.0154 | 15.40 |
| `write_fixed(10, 10000)` | 0.1645 | 0.1586..0.1688 | 0.15 | 0.1460 | 14.60 |

successive net ratios — 100→1000: ×5.92 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×9.48 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(i) 1,000 element reads `xs[0]`, slice length m varying** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `read_fixed(10, 1000)` | 0.0356 | 0.0347..0.0364 | 0.03 | 0.0171 | 17.10 |
| `read_fixed(100, 1000)` | 0.0357 | 0.0348..0.0368 | 0.03 | 0.0172 | 17.20 |
| `read_fixed(1000, 1000)` | 0.0361 | 0.0354..0.0397 | 0.03 | 0.0176 | 17.60 |
| `read_fixed(10000, 1000)` | 0.0358 | 0.0351..0.0361 | 0.03 | 0.0173 | 17.30 |

successive net ratios — 10→100: ×1.01 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 100→1000: ×1.02 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 1000→10000: ×0.98 (linear ×10.0, quadratic ×100.0, cubic ×1000.0)

**(c) aggregate shape — 100 writes each** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| struct{y,x int}: s.x = i | 0.0211 | 0.0200..0.0219 | 0.01 | 0.0026 | 26.00 |
| struct{a [100]byte; x int}: s.x = i | 0.0202 | 0.0199..0.0212 | 0.01 | 0.0017 | 17.00 |
| struct{a [1000]byte; x int}: s.x = i | 0.0212 | 0.0200..0.0218 | 0.01 | 0.0027 | 27.00 |
| struct{a [10000]byte; x int}: s.x = i | 0.0228 | 0.0213..0.0232 | 0.01 | 0.0043 | 43.00 |
| struct{a []byte; x int}, len(a)=100: s.x = i | 0.0210 | 0.0203..0.0217 | 0.01 | 0.0025 | 25.00 |
| struct{a []byte; x int}, len(a)=10000: s.x = i | 0.0232 | 0.0220..0.0233 | 0.01 | 0.0047 | 47.00 |
| [10000]byte: b[0] = v | 0.0227 | 0.0219..0.0233 | 0.01 | 0.0042 | 42.00 |
| [10][1000]byte: a[0][0] = v | 0.0227 | 0.0210..0.0234 | 0.01 | 0.0042 | 42.00 |
| [100][100]byte: a[0][0] = v | 0.0229 | 0.0218..0.0229 | 0.01 | 0.0044 | 44.00 |
| [][]byte 10×1000 (separate cells): xs[0][0] = v | 0.0233 | 0.0230..0.0234 | 0.01 | 0.0048 | 48.00 |

**(d) allocation-only loops** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_new(1000,)` | 0.0570 | 0.0532..0.0605 | 0.05 | 0.0385 | 38.50 |
| `alloc_new(4000,)` | 0.2819 | 0.2797..0.2989 | 0.27 | 0.2634 | 65.85 |
| `alloc_new(16000,)` | 3.6743 | 3.6045..3.6808 | 3.66 | 3.6558 | 228.49 |
| `alloc_new(32000,)` | 14.1421 | 13.5869..14.1918 | 14.13 | 14.1236 | 441.36 |

successive net ratios — 1000→4000: ×6.84 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×13.88 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 16000→32000: ×3.86 (linear ×2.0, quadratic ×4.0, cubic ×8.0)

**(d′) `make([]byte, 4)` per iteration (the 2026-09-03 audit probe)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `alloc_make4(1000,)` | 0.0527 | 0.0520..0.0555 | 0.04 | 0.0342 | 34.20 |
| `alloc_make4(4000,)` | 0.2673 | 0.2663..0.2700 | 0.26 | 0.2488 | 62.20 |
| `alloc_make4(16000,)` | 3.4248 | 3.4167..3.4344 | 3.41 | 3.4063 | 212.89 |

successive net ratios — 1000→4000: ×7.27 (linear ×4.0, quadratic ×16.0, cubic ×64.0); 4000→16000: ×13.69 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) live-heap size h vs a fixed 20,000-iteration scalar loop — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 0)` | 0.0202 | 0.0194..0.0204 | 0.01 | 0.0017 | — |
| `heap_then_scalar(1000, 0)` | 0.0494 | 0.0480..0.0508 | 0.04 | 0.0309 | 30.90 |
| `heap_then_scalar(10000, 0)` | 1.1990 | 1.1982..1.2115 | 1.19 | 1.1805 | 118.05 |
| `heap_then_scalar(40000, 0)` | 17.8546 | 17.8380..18.2198 | 17.84 | 17.8361 | 445.90 |

successive net ratios — 1000→10000: ×38.20 (linear ×10.0, quadratic ×100.0, cubic ×1000.0); 10000→40000: ×15.11 (linear ×4.0, quadratic ×16.0, cubic ×64.0)

**(h) … allocation phase + scalar phase (w = 20000)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_scalar(0, 20000)` | 0.2785 | 0.2753..0.2951 | 0.27 | 0.2600 | 13.00 |
| `heap_then_scalar(1000, 20000)` | 0.4342 | 0.4313..0.4473 | 0.42 | 0.4157 | 20.78 |
| `heap_then_scalar(10000, 20000)` | 2.9829 | 2.9491..3.0863 | 2.97 | 2.9644 | 148.22 |
| `heap_then_scalar(40000, 20000)` | 24.6814 | 24.6575..24.7017 | 24.67 | 24.6629 | 1233.14 |

scalar-phase cost at heap size h (= (h, 20000) net − (h, 0) net):
  h=0: 0.2583 s
  h=1000: 0.3848 s
  h=10000: 1.7839 s
  h=40000: 6.8268 s

**(h′) live-heap size h vs 300 in-place appends — allocation phase alone (w = 0)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 0)` | 0.0199 | 0.0190..0.0210 | 0.01 | 0.0014 | — |
| `heap_then_append(10000, 0)` | 1.3005 | 1.2994..1.3187 | 1.29 | 1.2820 | 128.20 |
| `heap_then_append(40000, 0)` | 18.2524 | 18.2097..18.8774 | 18.24 | 18.2339 | 455.85 |

**(h′) … + 300 in-place appends (w = 300)** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `heap_then_append(0, 300)` | 0.0302 | 0.0300..0.0309 | 0.02 | 0.0117 | 39.00 |
| `heap_then_append(10000, 300)` | 1.3851 | 1.3840..1.3958 | 1.38 | 1.3666 | 4555.33 |
| `heap_then_append(40000, 300)` | 18.9143 | 18.4886..19.0379 | 18.90 | 18.8958 | 62986.00 |

append-phase cost at heap size h (= (h, 300) net − (h, 0) net):
  h=0: 0.0103 s
  h=10000: 0.0846 s
  h=40000: 0.6619 s

**(g) map writes, n distinct int keys** (3 runs per point; wall s median, min..max; cpu = user+sys median; net = median wall − empty-probe median)

| point | wall med | spread | cpu | net | per-op µs |
|---|---:|---|---:|---:|---:|
| `map_write(500,)` | 0.0289 | 0.0289..0.0299 | 0.02 | 0.0104 | 20.80 |
| `map_write(1000,)` | 0.0410 | 0.0395..0.0421 | 0.03 | 0.0225 | 22.50 |
| `map_write(2000,)` | 0.0771 | 0.0760..0.0784 | 0.07 | 0.0586 | 29.30 |
| `map_write(4000,)` | 0.1967 | 0.1959..0.2041 | 0.19 | 0.1782 | 44.55 |

successive net ratios — 500→1000: ×2.16 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 1000→2000: ×2.60 (linear ×2.0, quadratic ×4.0, cubic ×8.0); 2000→4000: ×3.04 (linear ×2.0, quadratic ×4.0, cubic ×8.0)
