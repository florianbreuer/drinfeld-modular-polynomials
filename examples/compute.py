# -*- coding: utf-8 -*-
r"""
Compute a Drinfeld modular polynomial from the command line and print its
coefficients in factored form.

    sage examples/compute.py Q N [--place P] [--zero] [--save FILE]

Examples:

    sage examples/compute.py 2 "T^2+T+1"          # Table 1 of the paper
    sage examples/compute.py 3 "T^2+1" --place "T+1"
    sage examples/compute.py 4 "T+y"              # y generates F_4 over F_2
    sage examples/compute.py 2 "T^5+T^2+1" --zero # only Phi_N(X,0)

In the output, the factor of each coefficient a_(m,n) with m + n < psi(N) that
is predicted by Theorem 1.2(1) of the paper, namely

    prod_{deg P = 1, P not dividing N} P^((q+1)(psi(N) - m - n)),

is printed first, in square brackets.
"""
from __future__ import print_function

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sage.all import GF, PolynomialRing, ZZ, sage_eval

from drinfeld_modpoly import (drinfeld_modular_polynomial,
                              drinfeld_modular_polynomial_at_zero, psi, monic_primes,
                              valuation)
from drinfeld_modpoly.database import save_polynomial
from drinfeld_modpoly.display import factored


def main(argv):
    opts = {"--place": None, "--save": None}
    args, i, zero = [], 0, False
    while i < len(argv):
        if argv[i] in opts:
            opts[argv[i]] = argv[i + 1]
            i += 2
        elif argv[i] == "--zero":
            zero = True
            i += 1
        else:
            args.append(argv[i])
            i += 1
    if len(args) != 2:
        print(__doc__)
        return 2
    q = ZZ(args[0])
    Fq = GF(q) if q.is_prime() else GF(q, 'y')
    A = PolynomialRing(Fq, 'T')
    names = {"T": A.gen(), "y": Fq.gen()}
    parse = lambda s: A(sage_eval(s.replace("^", "**"), locals=names))
    N = parse(args[1])
    place = parse(opts["--place"]) if opts["--place"] else None
    compute = drinfeld_modular_polynomial_at_zero if zero else drinfeld_modular_polynomial
    Phi, cert = compute(N, place=place, certificate=True, verbose=True)
    ps = psi(N)
    deg1 = [P for P in monic_primes(A, 1) if not P.divides(N)]
    print()
    print("%s for q = %s, N = %s  (psi(N) = %s, %.1fs)"
          % ("Phi_N(X,0)" if zero else "Phi_N(X,Y)", q, N, ps, cert["seconds"]))
    if zero:
        items = sorted(((m, 0), c) for m, c in Phi.dict().items())
    else:
        items = sorted(((k[0], k[1]), c) for k, c in Phi.dict().items() if k[0] >= k[1])
    for (m, n), a in items:
        k = (q + 1) * (ps - m - n)
        if k > 0 and deg1:
            assert all(valuation(a, P) >= k for P in deg1), "Theorem 1.2(1) violated?!"
            pred = A.prod(P ** k for P in deg1)
            rest = a // pred
            txt = "[%s]%s" % (factored(pred),
                              "" if rest == 1 else " * " + factored(rest, bare=False))
        else:
            txt = factored(a)
        print("  a_(%d,%d) = %s" % (m, n, txt))
    if not zero:
        print("  (a_(m,n) = a_(n,m); coefficients not listed are zero)")
    if opts["--save"]:
        save_polynomial(opts["--save"], Phi, N,
                        {"place": str(cert["place"]), "precision_K": int(cert["precision"]),
                         "height_bound": int(cert["height_bound"])})
        print("saved to", opts["--save"])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
