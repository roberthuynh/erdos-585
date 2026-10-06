"""Print alpha/beta petals of a C2 graph and the alpha pairs with a (2,0)/(0,2) split (lane qb5).
Exhaustive over vertex sets; meant for n <= 20. Usage: split_detail.py < file.g6 (first graph with a split)."""
import sys
from itertools import combinations
from g6 import decode

def analyze(line, show=True):
    n, adj = decode(line)
    col = [-1]*n; col[0] = 0; st = [0]
    while st:
        v = st.pop()
        for u in adj[v]:
            if col[u] < 0: col[u] = 1-col[v]; st.append(u)
    c0 = [v for v in range(n) if col[v] == 0]; c1 = [v for v in range(n) if col[v] == 1]
    U, W = (c0, c1) if len(c0) < len(c1) else (c1, c0)
    Um = sum(1<<v for v in U); Wm = sum(1<<v for v in W)
    deg = [len(adj[v]) for v in range(n)]
    full = (1<<n)-1
    A = [sum(1<<u for u in adj[v]) for v in range(n)]
    def e(S):
        t = 0
        for v in range(n):
            if S>>v&1: t += bin(A[v]&S).count('1')
        return t//2
    def f(S):
        sW = S&Wm; sU = S&Um
        cross = sum(bin(A[v]&(Um&~sU)).count('1') for v in range(n) if sW>>v&1)
        return cross - 4*(bin(sW).count('1')-bin(sU).count('1'))
    def kap(S): return bin(S&Um).count('1')-bin(S&Wm).count('1')
    def g(S): return 6*bin(S).count('1')-2*e(S)
    pet = {}
    for S in range(full+1):
        if (S&Wm) == Wm: continue
        fs = f(S)
        if fs < 0:
            Q = full&~S
            k = bin(S&Wm).count('1')-bin(S&Um).count('1')
            DC = sum(6-deg[v] for v in U if S>>v&1)
            pet[Q] = (fs, k, DC, g(Q), kap(Q))
    alpha = [Q for Q,(fs,k,DC,gq,kq) in pet.items() if k==2 and fs==-1 and DC==0]
    splits = []
    for Q, Q2 in combinations(alpha, 2):
        I, Un = Q&Q2, Q|Q2
        if (kap(I), kap(Un)) != (1, 1): splits.append((Q, Q2, kap(I), kap(Un), g(I), g(Un)))
    return n, U, W, deg, pet, alpha, splits

def fmt(S, n): return '{' + ','.join(str(v) for v in range(n) if S>>v&1) + '}'

def main():
  for line in sys.stdin:
      line = line.strip()
      if not line: continue
      n, U, W, deg, pet, alpha, splits = analyze(line)
      if not splits: continue
      print(line); print('U =', U, 'W =', W, 'deg =', deg)
      print('number of violating sets', len(pet), 'alpha petals', len(alpha))
      minimal = [Q for Q in pet if not any(Q2 != Q and Q2 & Q == Q2 for Q2 in pet)]
      for Q in sorted(minimal, key=lambda q: bin(q).count('1')):
          print(' minimal petal', fmt(Q, n), 'sigma,k,D(C),g,kappa =', pet[Q])
      for s in splits[:6]:
          print(' split', fmt(s[0], n), fmt(s[1], n), 'kappa(cap,cup) =', s[2], s[3], 'g =', s[4], s[5])
      break


if __name__ == "__main__":
    main()
