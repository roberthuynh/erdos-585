#!/bin/bash
# Check 3: unpruned n = 16 spot-check on shards of plain geng -d5 -D5 16 r/20000, taken in the
# recorded random order data/check3_shard_order.txt (Python 3.9 random.Random(20261006).sample(range(20000), 400)).
# 4 workers; no shard starts at or after CUTOFF (epoch seconds, first argument).
LANE=[local path]
export CUTOFF=$1
echo "start $(date '+%F %T') cutoff $(date -r "$CUTOFF" '+%F %T')"
xargs -P 4 -I{} /bin/bash "$LANE/code/shard16.sh" check3 {} 20000 < "$LANE/data/check3_shard_order.txt"
echo "end $(date '+%F %T')"
