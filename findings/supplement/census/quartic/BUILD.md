# Independent nauty 2.9.3 build (M2 census lane)

Built 2026-10-04 23:37 EDT on aarch64-apple-darwin25.6.0, Apple clang 21.0.0 (clang-2100.1.1.101).
Source: `nauty2_9_3.tar.gz` (the nauty 2.9.3 release archive), SHA-256
`9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b`. A separate nauty build in a temporary folder was not touched.

```
mkdir -p ~/.cache/erdos585
cd ~/.cache/erdos585
tar -xzf nauty2_9_3.tar.gz
cd nauty2_9_3
./configure > configure.log 2>&1
make geng genbg labelg > make.log 2>&1
```

Link lines from `make.log` (no PRUNE hook, stock source):

```
gcc -O3 -march=native -o geng  -DMAXN=WORDSIZE -DWORDSIZE=32 geng.c  gtoolsW.o nautyW1.o nautilW1.o naugraphW1.o schreierW.o naurng.o
gcc -O3 -march=native -o genbg -DMAXN=WORDSIZE -DWORDSIZE=32 genbg.c gtoolsW.o schreierW.o nautyW1.o nautilW1.o naugraphW1.o naurng.o
gcc -O3 -march=native -o labelg labelg.c naututil.o traces.o nauty.o nautil.o nausparse.o naugraph.o schreier.o naurng.o gtnauty.o nautinv.o gtools.o
```

| Binary | Path | SHA-256 |
|---|---|---|
| geng 2.9.3 | `~/.cache/erdos585/nauty2_9_3/geng` | `588052a87e5313f331aa145a0a641702b6c13b6e2387dd3c4807bf7f49fdaca1` |
| genbg 2.9.3 | `~/.cache/erdos585/nauty2_9_3/genbg` | `502f5f46e613f9eefa905a2c521f06f45d0737854374bbd60e6929f45f4ef957` |
| labelg 2.9.3 | `~/.cache/erdos585/nauty2_9_3/labelg` | `ae8b1e7ef173c1665725e708bd7abd00b08ee4230ba2bd04117ec63d441274a0` |

Note: this geng is byte-identical to `geng` (same SHA-256), the binary the
original F2 census used. Same source and compiler give the same bytes, so for F2 the independent
generator is `geng_q4` (nauty 2.8.9 plus the q4 PRUNE), not this geng.

Tools reused read-only (not rebuilt; `build.sh` was not run):

| Binary | SHA-256 |
|---|---|
| `reports/585-fable-wildcard/lanes/quartic-subgraph/geng_q4` (2.8.9 + q4prune) | `8b4d578371464cf7b32d1d02a1f0da45e2ce2c96c3651d88139259b3ea0f0656` |
| `reports/585-fable-wildcard/lanes/quartic-subgraph/genbg_q4` (2.8.9 + q4prune_bg) | `a29067acd4d5a611fb56321f5eed7910bf90fc6db7712d0261eec4ebbd84404c` |
| `reports/585-fable-wildcard/lanes/quartic-subgraph/q4filter` | `30e4fe64d2d5fc03d16288a1838056e22ed61a20786600ea14219cc308c9ed4d` |
