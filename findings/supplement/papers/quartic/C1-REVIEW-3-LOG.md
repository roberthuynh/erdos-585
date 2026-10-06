# Referee log: C1-PAPER.md (independent adversarial referee, Fable lane)

## 15:11 EDT
- Frozen hash check at start: `C1-PAPER.md: OK`.
- Created folder reports/585-next/wave4/c1-fable-ref/ with code/.
- Not opening C1-REVIEW.md, C1-CORRECTIONS.md, review-c1/, wave3/ref2/ until my verdict is written.
- Plan: read the paper end to end, then attack Lemma 2.1, 3.2, 4.1, 4.2, the three-set count in Thm 4.3, Cor 5.4; check cited inputs (REPORT.md Theorem 5, E4->C1, E3->C0, Olson); write my own code.

## 15:20 EDT
- Read C1-PAPER.md end to end (487 lines). Hand re-derivation, first pass, of Identities 1.1-1.3, Lemma 1.4 (flow criterion via max-flow/min-cut), Lemma 1.5, (M), Lemma 2.1, basic counts, Lemma 3.1 (full expansion), Lemma 3.2, Lemmas 4.1, 4.2, Thm 4.3, Cor 5.1-5.4, and the Tutte budget identity of §5.4 (derived w(C) = 2D_C + e(C,S) + 2e(C,T) - 3[e(C,S) odd] myself; parity condition of q reduces to e(C,S) odd). No error found yet on the first pass.
- Next: pull the cited line ranges of PAPER.md, REPORT.md, QUARTIC-REVIEW.md and compare against the paper's claims; then code.

## 15:27 EDT
- Cited sources pulled and compared: PAPER.md 53-60 (classes, gadget = B - o), 87-122 (Lemma 0.1 flow criterion, Lemma 0.2 Olson group-ring), 141-157 (E3 reduction), 573-590 (sub-case counts); REPORT.md 130-221 (Lemma 1 Tutte, Lemma 2 budget identity with w(C) = 2D_C + e(C,S) + 2e(C,T) - 3[e(C,S) odd], Lemma 4, Theorem 5 c = 2 type), 236-267 (reductions E3->C0, E4->C1, C0 and C1 steps); QUARTIC-REVIEW.md 17-21, 82-104; CORRECTIONS.md census bounds m <= 41/59/62.
- All quotes in C1-PAPER.md match the sources' own text so far. My own derivation of w(C) agrees with REPORT.md Lemma 2 exactly.

## 15:21 EDT
- Wrote code/ref_common.py (own helpers: Bip, SAT quartic decider with exact forbidden-assignment encoding, flow 4-factor, random C1 generator) and code/check_identities.py; ran it (see out_identities.json).

## 15:22 EDT
- Identity run PASS: 102 random C1 instances, I1-I3 on 6,291,456 cuts, I4 criterion vs max flow on 546 ports, I5 on 12 violations with g(Q) >= 10 (all profile (2,-1,10,0)), J1 306,000 pairs, J2/J4/J6 1,198,370 sets, 0 mismatches. L15 hit only 2 violations (random E4 rarely lacks a 4-factor); strengthening in adversarial.py.
- Launched exhaustive_small.py for s = 5, 6, 7 in background (genbg -d5:0 -D6:6 s s+1 6s-1:6s, own SAT decider).

## 15:23 EDT
- Wrote code/sparse_core.py (own sub-case builder; exact sparsity by subset DP; full enumeration of the family P; checks E, L41, L42 on all pairs, L44). Launched seeds 1, 2 in background.

## 15:24 EDT
- Exhaustive Theorem 4.3 check at s = 5, 6, 7 (every C1 instance up to isomorphism, W-degree >= 0, D_U in {0,1}): PASS, see out_exhaustive_s*_all.json. Wrote code/tutte_budget.py (T1 Tutte form vs SAT 4-factor over all 3^n pairs; T2 budget identity and (**); T3 P_2 exhaustive via geng n = 7..10; T4 barrier type of e = 3n-2, delta >= 4 graphs without a 4-factor); launched.

## 15:25 EDT
- Wrote code/adversarial.py (R1 random C1 search for a quartic-free instance, R2 all-ports-bad instances must be non-sparse, R3 Lemma 1.5 on E4 instances built to lack a 4-factor); launched seeds 7, 8. Waiting on sparse_core and tutte runs.

## 15:30 EDT
- sparse_core seed 2 (first version): 24 built, 19 exactly sparse (min g = 10 over proper sets, subset DP up to n = 25); bad ports total deficiency <= 2 in all 19; one instance had two members of P (nested). The 85 "E" failures were MY bug: I required w to be a bad *port*, but Lemma 3.1 holds for every W-vertex y, so degree-6 W-vertices of a petal also have G - w without a 4-factor (not a paper error). Fixed (E) to check that directly by flow. Seed 1 was killed by timeout 240 at n = 25 (2^25 DP); capped at n <= 23 and budget 150. Added a nesting bias (y of degree 4 adjacent to an x with three T-edges) to produce chains in P.
- Side derivation (my own, not in the paper): in any sparse C1 instance with D_U = 1 the family P is a chain. Proof sketch in REVIEW.md. Explains why no builder produces incomparable petals.

## 15:34 EDT
- REVIEW.md drafted (verdict ACCEPT, re-derivation, cited inputs table, code table, optional clarifications, observations); two placeholders left for the sparse_core numbers and the comparison section.

## 15:34 EDT
- Verdict written in REVIEW.md §1-§7 (ACCEPT). Now opening the other reviews for the comparison section only.

## 15:36 EDT
- Read C1-REVIEW.md, C1-CORRECTIONS.md and the verdict table of wave3/ref2/REVIEW.md. Adopted their R1 (line 242 drops "bipartite"; verified against the paper and CORRECTIONS.md). FINAL verdict in REVIEW.md: ACCEPT WITH FIXES (R1 wording only; every lemma, theorem and corollary ACCEPT). §8 comparison written.
- Frozen hash check at the end: C1-PAPER.md OK. Paper never edited. All work inside wave4/c1-fable-ref/.
