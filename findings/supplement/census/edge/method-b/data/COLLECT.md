# Method B collector output

Written 2026-10-06 10:52:51 EDT by `code/collect.py` from the shard files.

| Job | Command | Shards ok / total | Output graphs (no 4-regular subgraph) | Whole class (graphs generated) | CPU s (user) | Status |
|---|---|---|---|---|---|---|
| pr_n17_e44_8x9 | `bin/bipgen 8 9 44:44 4:4 6:6` | 1/1 | 0 | - | 2 | COMPLETE |
| pr_n17_e44_9x8 | `bin/bipgen 9 8 44:44 4:4 6:6` | 1/1 | 0 | - | 2 | COMPLETE |
| pr_n18_e47_8x10 | `bin/bipgen 8 10 47:47 4:4 6:6` | 1/1 | 0 | - | 11 | COMPLETE |
| pr_n18_e47_10x8 | `bin/bipgen 10 8 47:47 4:4 6:6` | 1/1 | 0 | - | 2 | COMPLETE |
| pr_n18_e47_9x9 | `bin/bipgen 9 9 47:47 4:4 6:6 {r}/{mod}` | 4/4 | 0 | - | 58 | COMPLETE |
| pr_n19_e51_9x10_d5 | `bin/bipgen 9 10 51:51 5:5 6:6` | 1/1 | 0 | - | 18 | COMPLETE |
| pr_n19_e51_10x9_d5 | `bin/bipgen 10 9 51:51 5:5 6:6` | 1/1 | 0 | - | 7 | COMPLETE |
| n19_e50_10x9 | `bin/bipgen 10 9 50:50 4:4 6:6 {r}/{mod}` | 50/50 | 0 | - | 855 | COMPLETE |
| n19_e50_9x10 | `bin/bipgen 9 10 50:50 4:4 6:6 {r}/{mod}` | 50/50 | 0 | - | 568 | COMPLETE |
| wh_n17_e44_8x9 | `bin/bipgen -P -q 8 9 44:44 4:4 6:6 \| bin/h4filt` | 1/1 | 0 | 14,087,019 (with H 14,087,019) | 53 | COMPLETE |
| wh_n18_e47_10x8 | `bin/bipgen -P -q 10 8 47:47 4:4 6:6 \| bin/h4filt` | 1/1 | 0 | 8,584,858 (with H 8,584,858) | 21 | COMPLETE |
| wh_n19_e51_10x9_d5 | `bin/bipgen -P -q 10 9 51:51 5:5 6:6 \| bin/h4filt` | 1/1 | 0 | 10,055,368 (with H 10,055,368) | 109 | COMPLETE |
| wh_n18_e47_9x9 | `bin/bipgen -P -q 9 9 47:47 4:4 6:6 {r}/{mod} \| bin/h4filt` | 200/200 | 0 | 1,316,086,566 (with H 1,316,086,566) | 3,447 | COMPLETE |

Total user CPU of the detached jobs: 5,151 s (1.43 core-h).

| n | e | min degree | sides | pruned runs (own generator + decider) | whole class, no pruning (own generator, every graph decided by h4filt) | method 1 class count (plain genbg) | verdict |
|---|---|---|---|---|---|---|---|
| 17 | 44 | >= 4 | 8+9 | pr_n17_e44_8x9: 0 graphs; pr_n17_e44_9x8: 0 graphs | 14,087,019 generated, 0 without H; = method 1: yes | 14,087,019 | EMPTY |
| 18 | 47 | >= 4 | 8+10 | pr_n18_e47_8x10: 0 graphs; pr_n18_e47_10x8: 0 graphs | 8,584,858 generated, 0 without H; = method 1: yes | 8,584,858 | EMPTY |
| 18 | 47 | >= 4 | 9+9 | pr_n18_e47_9x9: 0 graphs | 1,316,086,566 generated, 0 without H | - | EMPTY |
| 19 | 50 | >= 4 | 9+10 | n19_e50_10x9: 0 graphs; n19_e50_9x10: 0 graphs | - | - | EMPTY |
| 19 | 51 | >= 5 | 9+10 | pr_n19_e51_9x10_d5: 0 graphs; pr_n19_e51_10x9_d5: 0 graphs | 10,055,368 generated, 0 without H; = method 1: yes | 10,055,368 | EMPTY |

Chain (rules in EX-B.md section 3; ex(16) = 40 from `data/chain.txt`):
- ex(17) = 43: yes
- ex(18) = 46: yes
- ex(19) = 49: yes
