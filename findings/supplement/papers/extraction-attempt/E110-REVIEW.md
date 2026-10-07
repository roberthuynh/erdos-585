# Independent review of E110

Date: 2026-10-04. Final disposition: **accept the packet as a correct failure analysis with finite controls. E110 is unproved and unrefuted.** The registered mechanism is closed after its single repair. No E110 statement is recommended for promotion as a proved result.

Reviewed final `main-extraction/PAPER.md` SHA256:

`033c07c47a7a21d0e1c25628190aa54cd9b31301e283baae96d31bec1f3bf217`

The final manifest matches all five author files. Exact accepted hashes and independent finite-check outputs are in [E110-INDEPENDENT-CHECK.json](E110-INDEPENDENT-CHECK.json). The three requested precision corrections are present. No outstanding correction remains within this review's scope.

## Mathematical findings

| Claim | Decision and scope |
| --- | --- |
| Hall identity and failure inequality, Section 3 | Correct; they do not use avoidance. |
| Four-common-neighbor charge, Section 4 | Correct avoidance-dependent K4,4 bound; it does not control accumulated extraction loss. |
| Balanced 102-vertex control, Section 5 | Finite certificate independently verified; inherited avoidance uses the unchanged parent's prior PASS. |
| Actual-boundary gluing criterion, Section 6 | Correct with the stated common-support, path-component, incidence and multigraph conditions. |
| Nine-state inequality, Section 7 | Correct and sharp; no lower bound on actual realizable states follows. |
| E110 extraction conclusion | Not established. None of the controls refutes it. |

For a balanced bipartite graph with degree cap r, put `t=|X|-|Y|`, `a=e(X,Q\Y)` and `b=e(P\X,Y)`. Summing degrees in the two oriented sets gives exactly

    D_X-D_Y = r*t-a+b.

For integer `q=r-ell>0`, a failed q-factor cut has `a<q*t`, hence `t>0` and `D_X-D_Y>ell*t+b`. When all degrees are at least `(1-eta)r`, `ell=epsilon*r` and `0<=eta<epsilon<1`, the two strict bounds in (3.4) follow. These are ordinary factor-cut consequences. They provide no improvement specific to an avoider.

Avoidance does imply (4.1), since four common neighbors of four vertices would give an actual K4,4, which contains a pair. The convexity step and the resulting lower bound of order `r^(4/3)` on a concentrated Hall rectangle are correct under their stated `eta<epsilon` and positive-average hypotheses. This is an easy-end exclusion. It bounds neither the number of such rectangles nor their total defect, cut loss or retained degree. At `r` of order `(log N)^3`, its order bound is only of order `(log N)^4`. The paper correctly makes no E110 progress claim from it.

The Section 6 states retain actual cut-edge labels and actual red/blue internal witnesses on the same support. The formulation covers length-zero paths and repeated boundary vertices, and excludes closed internal color components when that color crosses the cut. Gluing compatible states therefore produces two disjoint connected 2-regular subgraphs with equal support in the original simple graph. Conversely, restricting a crossing pair produces such states. Keeping both side-colored matching edges when a label pair repeats is necessary in the two-label case and is now explicit.

For four labels of each cycle color, the compatibility relation is exactly coordinatewise inequality on `[3]^2`. The direct proof of `|Sigma_U|*|Sigma_W|<=9` for cross-incompatible families is sound and sharp. The larger fixed-pair matching families are correctly labeled abstract families, not graph realizations. They show why mere abstract incompatibility does not force a sufficiently small family.

**The unpaid step is quantitative and concerns actual witnesses.** The packet supplies no implication from the Hall data, cut boundary and degree information to lower bounds on actual common-support state families, or to a restriction on their concentration among incompatible pairings. It does not even establish a useful state on both sides. Consequently neither (4.1) nor (7.1) bounds successive relative degree losses or proves that the product of retained-degree fractions stays above an absolute positive constant. The repaired state definition cannot substitute for that estimate. There are genuine avoidance-conditioned inequalities here, but none pays E110's extraction obligation.

## Finite checks and result status

The independent script [e110_independent_check.py](e110_independent_check.py) reconstructs source adjacency without importing the author's checker and validates the supplied certificates. It was run once under `timeout 240`; all assertions passed. After the text corrections, only the final hashes were rechecked because the checker and control data were unchanged.

- The unchanged `BipartiteFive.lean` hash is `bbabb4afd5c48f064c7bfe596397d1b635f194f3bea7339a1ce9f7dbac61a0ec`, equal to the saved PASS receipt's proof hash.
- Deleting vertices 0 and 55 gives 102 vertices, 250 edges, shores 51 and 51, ten degree-four vertices and 92 degree-five vertices. The oriented Hall data are `(t,a,b,D_X,D_Y)=(1,1,1,5,0)`. Thus every spanning q-factor with integer q>=2 fails. The supplied 51-edge perfect matching is valid, so maximum spanning regular degree is exactly one.
- The supplied Q4 cycles are valid, edge-disjoint and spanning, with coordinate-cut crossing counts `(4,4),(6,2),(4,4),(2,6)`. Q4 has maximum pair codegree two and hence no K4,4. Its connected quartic structure forces every pair to use the whole host, including all eight edges of each coordinate cut. A four-total-crossing interface misses this control.
- Enumerating all 512 left families in the nine-state space gives maximum cross-incompatible size product nine.

These checks did not search for avoidance or run Lean or `check.sh`. H102's avoidance is a paper consequence of deletion from the prior checked parent. It is a finite control, not a new kernel theorem, not an E110 counterexample, and not a counterexample to Lemma F: the needed expansion and much tighter relative degree spread are absent.

## Synthesis and BM scope

Within the assigned E110/BM scope, the current `FINAL-SYNTHESIS.md` uses the inputs and terminal outcome correctly. The balanced near-regular extension is already supplied by reviewed local Lemma F; reproving it would not pay E110. For E110's fixed `gamma_0` and `k>=16/gamma_0^2`, F yields a factor degree at least `k/2` and BJ expansion parameter at least `gamma_0/4`. Thus a sufficiently large absolute A can pay BM-2's degree and expansion constants, with `log h<=log(2N)`. The subsequent `O(n(log n)^4)` ledger remains conditional on E110 and the stated local BM/CJMM inputs.

BM is a reviewed local paper argument, not a kernel-checked result in this pass. Its growing `log^3` degree threshold gives no degree-six statement. A full Hamilton decomposition of a suitable host would imply a pair, while a pair only gives a Hamilton-decomposable quartic subgraph on its own support; the reverse host-level implication is absent. The exact published-source qualifications are recorded in the orientation review (not included). This review does not certify other lanes of the final synthesis.

No author/source edits, new mathematical route, Lean/oracle command, public action or Git action was performed by this reviewer. Root owns the combined report and result classification. The requested review is complete.
