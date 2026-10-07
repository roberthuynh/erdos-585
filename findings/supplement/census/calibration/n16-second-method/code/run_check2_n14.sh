#!/bin/bash
# Check 2 at n = 14: 40 shards of plain geng -d5 -D5 14, 4 workers.
LANE=[local path]
echo "start $(date '+%F %T')"
seq 0 39 | xargs -P 4 -I{} /bin/bash "$LANE/code/shard.sh" check2 14 {} 40
echo "end $(date '+%F %T')"
