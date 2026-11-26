"""Exact regression of the finite-rank Schur update and error algebra.

These matrix cases do not prove the Hilbert-space or domain hypotheses.
"""
from fractions import Fraction as F


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def solve(A, b):
    M = [[F(x) for x in row]+[F(y)] for row, y in zip(A, b)]
    n = len(M)
    for j in range(n):
        pivot = next(i for i in range(j,n) if M[i][j])
        M[j], M[pivot] = M[pivot], M[j]
        f = M[j][j]
        M[j] = [x/f for x in M[j]]
        for i in range(n):
            if i != j:
                f = M[i][j]
                M[i] = [x-f*y for x,y in zip(M[i],M[j])]
    return [row[-1] for row in M]


def schur():
    count = 0
    for n in (1,2,3):
        d = 2*n
        for m in (1,2,5):
            for seed in range(1,9):
                # Euclidean model of H_k; includes rank-deficient P and G.
                P = [[F((i+2*j+seed)**2 % 11-5, j+1)
                      for j in range(m)] for i in range(d)]
                D = [F(i+seed, i+2) for i in range(d)]
                a = [F((i+seed)%7-3, i+1) for i in range(d)]
                G = [[dot(P[i],P[j]) for j in range(d)] for i in range(d)]
                A = [[G[i][j]+(1/D[i] if i==j else 0)
                      for j in range(d)] for i in range(d)]
                v = solve(A, a)
                w = [-dot(col,v) for col in zip(*P)]
                residual = [a[i]+dot(P[i],w) for i in range(d)]
                assert residual == [v[i]/D[i] for i in range(d)]
                cost = dot(w,w)+sum(di*ri*ri for di,ri in zip(D,residual))
                assert cost == dot(a,v)
                assert 0 <= cost <= sum(di*ai*ai for di,ai in zip(D,a))
                for j in range(m):
                    assert w[j]+sum(P[i][j]*D[i]*residual[i] for i in range(d)) == 0
                h = [F(i-seed, i+1) for i in range(m)]
                displaced = [residual[i]+dot(P[i],h) for i in range(d)]
                wh = [wi+hi for wi,hi in zip(w,h)]
                assert (dot(wh,wh)+sum(di*ri*ri for di,ri in zip(D,displaced))
                        == cost+dot(h,h)+sum(di*dot(row,h)**2 for di,row in zip(D,P)))
                count += 1
    print(f'{count} rational multi-mode Schur cases passed')


def errors():
    count = 0
    for den in range(2,31):
        for num in range(1,den):
            t = F(num,den)
            eps = lambda n: 2*t**(2*n)/(1-t**(2*n))
            rem = 4*t**4/(1-t*t)**2
            assert eps(1)**2 == rem
            assert eps(2)*(1+eps(1)) == rem/2
            assert eps(1)-2*t*t == 2*t**4/(1-t*t)
            assert eps(1)-2*t*t+eps(2)*(1+eps(1)) <= rem
            for n in range(1,13):
                assert eps(n+1) < eps(n)
                # Lower bound used in sharpness has the same leading order.
                assert eps(n)/(1+eps(1)) <= eps(n)
            count += 1
    print(f'{count} rational multipole error-bound cases passed')


if __name__ == '__main__':
    schur()
    errors()
