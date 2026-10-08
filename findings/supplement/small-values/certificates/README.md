# Complete saved upper certificates at orders 11 and 12

This packet gives computational upper exclusions f(11)≤31 and f(12)≤36. The original Lean lower witnesses give the reverse inequalities. The upper exclusions are not Lean theorems, and the values already appeared in v0.3.

For f(11), first check every one of the 395,166 ten-vertex graphs with 28 edges. Each has a literal cycle-pair certificate, proving f(10)≤27. A hypothetical pair-free 11-vertex graph with 32 edges then has minimum degree five and some degree-five vertex. Deleting it leaves a ten-vertex pair-free graph with 27 edges and minimum degree at least four. The complete stream has 217,596 representatives; positive certificates discard all but seven. All 137 admissible five-neighbor extensions of those parents have explicit pairs, a contradiction.

For f(12), first exclude the 11-vertex, 31-edge class of minimum degree five. Delete a degree-five vertex to reach ten vertices, 26 edges and minimum degree at least four. Of 203,469 generated parents, 500 are retained. All 2,367 admissible five-neighbor extensions have explicit pairs. Now a hypothetical 12-vertex pair-free graph with 37 edges has minimum degree at least six and a degree-six vertex. Its deletion gives the excluded 11-vertex class.

The complete ten-vertex streams contain 816,231 graphs, with 815,724 literal positive rejections and 507 retained parents. The additional 2,504 extensions all have literal positive certificates. Retained rows are checked as exactly the unmatched subsequence of the full stream. Every admissible ten-bit neighborhood mask is independently enumerated. For soundness, no negative answer by the search detector is trusted: every rejected graph has an actual pair, and every retained row is extended.

Generation coverage still relies on nauty's graph-isomorphism algorithm. The separate search and certificate verification are not separate canonical generators. `vendor/` preserves the original geng source and its copyright/license notice. nauty object files and headers are external dependencies for regenerating the streams; they are not represented as bundled files.

To check the saved certificates from the repository root:

```bash
cd findings/supplement/small-values/certificates
python3 -B verify_full_streams.py
python3 -B verify_certificates.py
```

The first summary must report 816231 graphs and 815724 positive rejections, with `complete: true`; the second must report 2367 and 137 verified extensions, also complete. These commands write only local validation receipts in this packet. They do not run a new generator census. The provided coverage receipts preserve saved counts and hashes. Original generator, tee and decider command arrays (including machine paths and arguments), binaries, generator and decider logs, and binary-build receipts are not bundled. Their saved log and binary hashes identify historical artifacts rather than bundled originals; the graph streams, catalogues and cycle certificates can be checked here.

For a full fresh computational replay, supply a built nauty 2.9.3 directory containing the required 32-bit objects and headers, and run `FINITE_NAUTY_DIR=<YOUR_NAUTY_BUILD_DIRECTORY> bash FRESH_REPLAY.sh`. This requires a C compiler, Python 3 and the `timeout` command; all long commands have a 240-second bound. The replay always uses the local `geng_plain` built from `vendor/geng.c`; `FINITE_GENG_BIN` does not select another generator. New build receipts and generation logs are written locally. Look for `COMPLETE COMPUTATIONAL CERTIFICATE`. A timeout is incomplete, not an empty exclusion.
