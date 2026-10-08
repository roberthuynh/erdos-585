# Prior work and references

This note records prior work related to results already in v0.3. It provides attribution and comparisons, without claiming a complete literature search or priority clearance. A quartic here means a nonempty 4-regular subgraph. QB(5) concerns finite simple bipartite graphs with n ≥ 3, maximum degree at most six and at least 3n − 5 edges.

| Topic | Earlier mathematics | Scope of this repository's comparison |
|---|---|---|
| Quartic extraction | Alon, Friedland and Kalai, *Regular subgraphs of almost regular graphs* (1984), Remark 3.6: bipartite hosts of maximum degree at most seven at 3n−2 edges | QB(5) has a maximum-degree-six hypothesis and 3n−5 threshold. The earlier remark does not directly give that threshold. Both statements conclude quartic extraction; neither asserts a Hamiltonian decomposition or a cycle pair. |
| Zero-sum selection | AFK Theorem 2.1 credits Olson's finite abelian zero-sum theorem; Alon's *Tools from Higher Algebra*, Theorem 6.2, gives an inspected statement and proof | Original Olson pages remain an access gap. The selection principle is prior mathematics, even when found independently in this project. |
| Twin/Euler lift | Eppstein, *Hamiltonian Cycles in Subdivided Doubles*, arXiv:2510.18359v1, Theorems 1 and 2 | The subdivided-double Hamilton lift is known. Any actual-host density application needs its separate embedding and selection hypotheses. |
| Five-regular obstructions | Read and Wilson, *An Atlas of Graphs* (1998), Chapter 5, p.155 | Generic five-regular graphs without a quartic are already recorded. Exact witness orders, bipartite restrictions and minimum-order census claims require additional comparison and evidence. |
| Sidon palettes | Huang, Tait and Won, *Sidon sets and 2-caps in F_3^n* (2019), Theorems 3.2 and 3.4; Cilleruelo's Example 1 (arXiv:1003.3576v2, 2011) | Sidon/2-cap equivalence and the parabola construction are prior geometry. The proposed contribution is its specific recoloring-detector application. |
| Haar decompositions | Bermond, Favaron and Mahéo (1989), Main Theorem, for connected quartic abelian Cayley graphs; Zhou et al., arXiv:1810.07866v1, Theorem 3, for the stated prime dihedral case | These cover specified identified Haar cases. They do not establish a new general Haar decomposition or automatically cover every nonsymmetric or composite template. |
| Small values | [Erdős Problem a Day](https://erdosproblemaday.com/report/585), July 28, 2026, Section 3 (read October 8, 2026) | Values through n = 10 were previously reported. Exact values are Lean-checked through n = 7; at n = 8, 9 and 10, upper exclusions are computational. The entries f(11) = 31 and f(12) = 36 already appear in v0.3 and extend that report. |

Alejandro Zarzuelo Urdiales's *Robert: eight-family novelty and current proof scope* and *Five-family primary-literature comparison*, both dated October 7, 2026, informed these literature and proof-coverage comparisons. This credit identifies that comparison work; it does not establish human verification of this repository's proofs.

## References

The references below support the comparisons above and the existing public findings. [REFERENCES.json](REFERENCES.json) supplies the same bibliographic data in machine-readable form.

- Noga Alon, Shmuel Friedland, Gil Kalai. [*Regular subgraphs of almost regular graphs*](https://web.math.princeton.edu/~nalon/PDFS/Publications/Regular%20subgraphs%20of%20almost%20regular%20graphs.pdf). JCTB 37 (1984), 79–91. Theorem 2.1 (Olson); Corollary 2.2; Theorem 3.1; Remark 3.6.

- Debsoumya Chakraborti, Oliver Janzer, Abhishek Methuku, Richard Montgomery. [*Edge-disjoint cycles with the same vertex set*](https://arxiv.org/abs/2404.07190). Advances in Mathematics 469 (2025), 110228. Theorems 1 and 2.

- Oliver Janzer, Benny Sudakov. [*Resolution of the Erdős–Sauer problem on regular subgraphs*](https://arxiv.org/abs/2204.12455). Forum of Mathematics, Pi 11 (2023), e19. Main fixed-degree theorem.

- Jean-Claude Bermond, Odile Favaron, Maryvonne Mahéo. [*Hamiltonian decomposition of Cayley graphs of degree 4*](https://hal.inria.fr/hal-02500476/file/67-BFM89-hamilton-cayley-degree4.pdf). JCTB 46(2) (1989), 142–153. Unnumbered Main Theorem.

- Yixuan Huang, Michael Tait, Robert Won. [*Sidon sets and 2-caps in F_3^n*](https://msp.org/involve/2019/12-6/involve-v12-n6-p06-p.pdf). Involve 12(6) (2019), 995–1003. Theorems 3.2 and 3.4; following parabola claim.

- David Eppstein. [*Hamiltonian Cycles in Subdivided Doubles*](https://arxiv.org/abs/2510.18359). Ars Mathematica Contemporanea 26 (4.02) (2026), 1–9; arXiv:2510.18359v1 (2025). Definitions 1–2; Theorems 1 and 2.

- Ronald C. Read, Robin J. Wilson. [*An Atlas of Graphs*](https://oeis.org/A000088/a000088_14.pdf). Oxford University Press (1998). Chapter 5, printed p.155; Theorem 11.

- John E. Olson. [*A combinatorial problem on finite Abelian groups, I*](https://doi.org/10.1016/0022-314X(69)90021-3). Journal of Number Theory 1(1) (1969), 8–10. Original theorem number unverified. The original full text was unavailable for this comparison. AFK Theorem 2.1 credits Olson; Alon's Tools from Higher Algebra, Theorem 6.2, gives the inspected statement and proof.

- Hui Zhou, Liufeng Xu, Yang Cui, Qi Ding, Yanfeng Luo, Xing Gao, Dong Yang. [*Hamiltonian decomposition of the Cayley graph on the dihedral group D_{2p} where p is a prime*](https://arxiv.org/abs/1810.07866v1). arXiv:1810.07866v1 (18 October 2018). Theorem 3; Lemma 5.

- Noga Alon. [*Tools from Higher Algebra*](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf). Author-hosted chapter; publication year and venue unverified in this comparison. Theorem 6.2 and its full group-ring proof. The citation identifies the author-hosted chapter; its publication year and venue have not been established in this comparison.

- Debsoumya Chakraborti, Oliver Janzer, Abhishek Methuku, Richard Montgomery. [*Regular subgraphs at every density*](https://doi.org/10.1090/tran/9694). Transactions of the AMS 379 (2026), 8069–8090; DOI 10.1090/tran/9694. Preprint v2 Theorems 1.4, 1.5 and 1.13. The listed theorem numbers refer to preprint v2; published numbering has not been independently compared.

- Javier Cilleruelo. [*Combinatorial problems in finite fields and Sidon sets*](https://arxiv.org/abs/1003.3576). Inspected preprint arXiv:1003.3576v2 (2011). Example 1.

- Patrick White; site discloses Claude (Anthropic) assistance. [*Erdős problem #585: live audit and exact small cases*](https://erdosproblemaday.com/report/585). Erdős Problem a Day working report, July 28, 2026. Section 3, table through n = 10. Working report; not a Lean proof or independent human review. Read October 8, 2026.
