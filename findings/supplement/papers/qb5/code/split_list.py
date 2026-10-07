"""Write the graphs of a file that have an alpha-petal pair with a (2,0) or (0,2) split (lane qb5)."""
import sys
from split_detail import analyze
for line in sys.stdin:
    line = line.strip()
    if line and analyze(line)[6]:
        print(line)
