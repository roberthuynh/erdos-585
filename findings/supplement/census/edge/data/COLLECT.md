# excensus collector output

Written 2026-10-06 03:28:11 EDT by `code/collect.py` from the shard files; rules in section 3.

| n | ex(n) | Basis |
|---|---|---|
| 17 | **43** | complete. e = 44 (sides 8 + 9): 0 graphs in both class orders; e ≥ 45: census F1(17); lower bound `data/witness_n17.g6` |
| 18 | **46** | complete. e = 47: sides 8 + 10, 0 graphs in both orders; sides 9 + 9 (job A), 0 graphs; e ≥ 48: census F1(18); lower bound `data/witness_n18.g6` |
| 19 | **49** | complete. e = 50 (job B, sides 9 + 10): 0 graphs; e = 51 forces δ ≥ 5 (Lemma B): 0 graphs in both orders; e ≥ 52: impossible (Lemma B; also QB(5)); lower bound `data/witness_n19.g6` |
| 20 | **52 or 53** | e ≥ 55 impossible (Lemma B); e = 54 forces δ ≥ 5 and job C (10 + 10) gave 0; e = 53 not run (over budget, section 5); lower bound `data/witness_n20.g6` |

So QB(7) (e ≥ 3n − 7 forces a nonempty 4-regular subgraph) holds for 4 ≤ n ≤ 19, and QB(6) holds for 4 ≤ n ≤ 20.

Detached jobs (`code/jobs.tsv`):

| Job | Class | Shards done | Output graphs (no 4-regular subgraph) | user CPU s | Status | Re-check of output |
|---|---|---|---|---|---|---|
| n18_99_e47 | n=18 e=47=3n-7 sides 9+9 delta>=4 | 40/40 | 0 | 2,057 | COMPLETE | - |
| n19_910_e50 | n=19 e=50=3n-7 sides 9+10 delta>=4 | 200/200 | 0 | 24,486 | COMPLETE | - |
| n20_1010_e54_d5 | n=20 e=54=3n-6 sides 10+10 delta>=5 | 200/200 | 0 | 5,575 | COMPLETE | - |
