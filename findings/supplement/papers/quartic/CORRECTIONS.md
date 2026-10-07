# Corrections to G110/PAPER.md (applied by reference; the reviewed file is left byte-identical)

PAPER.md SHA-256 `cfce4fcc7d40732c2f2a6c23b9d5fe50823c37f9d37f940b7857d8eda52ab0c9` is the version the
referee reviewed (REVIEW.md, overall verdict: no mathematical error; one required fix). This file
takes precedence over the paper where they differ.

## Fix F1 (required by REVIEW.md; provenance only, no statement changes)

PAPER.md lines 448 and 599-600 say the census facts F1 and F2 "rest on one program each" and were "not
re-run here". Replace with the census status recorded in `census/CENSUS.md` and `STATE.md`:

| Fact | Range | Methods |
|---|---|---|
| F1(N): bipartite, δ ≥ 4, Δ ≤ 6, e ≥ 3n − 6 ⇒ 4-regular subgraph | n ≤ 14 | two independent (geng_q4; plain geng 2.9.3 + pysat decider) |
| | n = 15, 16 | two (geng_q4; plain geng 2.9.3 + pysat) |
| | n = 17, 18 | one (genbg_q4) |
| F2(N): same with e ≥ 3n − 4 | n ≤ 18 | two independent (original plain geng + pairc; geng_q4 / genbg_q4), three at n = 18 |
| | n = 19 | two generators (genbg_q4, geng_q4) sharing the q4core.h decider |
| | n = 20 | running at the time of this note; not established |

Consequences with the paper's Theorem 3.3 form "C0 for m ≤ 3·N2 + 5 given F2(N2)": m ≤ 59 (N2 = 18,
two independent methods), m ≤ 62 (N2 = 19, one decider). Theorem 3.5 (m ≤ 41) uses no census.
