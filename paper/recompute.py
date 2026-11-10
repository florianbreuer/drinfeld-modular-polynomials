# -*- coding: utf-8 -*-
r"""
Recompute the Drinfeld modular polynomials of the paper from scratch.

    sage paper/recompute.py quick          # the 9 levels with psi(N) <= 6
    sage paper/recompute.py all            # all 20 Phi_N(X,Y) and all 24 Phi_N(X,0)
    sage paper/recompute.py zero           # only the 24 Phi_N(X,0)
    sage paper/recompute.py places         # other base places (q = 2, 3, 4)
    sage paper/recompute.py places-all     # ... and q = 9 at the places T + 1, T + y
    sage paper/recompute.py all --write    # regenerate the files in data/

Without ``--write`` every recomputed polynomial is compared, coefficient by
coefficient, with the certified polynomial stored in ``data/``.

Each computation uses the proven height bound of [BPR2024, Thm. 1.1] with 12
spare digits, so by Proposition 5.1 of the paper its output is the exact
Phi_N; the program itself checks that the spare digits vanish, that every
residue lies in F_P, that deg_T a_(m,n) <= h, and that Phi_N is monic and
symmetric.
"""
from __future__ import print_function

import sys
import time

from cases import levels, levels_at_zero, load, path, ring, Report

from sage.all import version
from drinfeld_modpoly import (drinfeld_modular_polynomial,
                              drinfeld_modular_polynomial_at_zero, psi)
from drinfeld_modpoly.database import save_polynomial


def record(cert):
    return {"place": str(cert["place"]),
            "precision_K": int(cert["precision"]),
            "height_bound": int(cert["height_bound"]),
            "E_degree_over_Fq": int(cert["extension_degree"]),
            "seconds": round(cert["seconds"], 1),
            "software": "drinfeld_modpoly 1.0.0, " + version()}


def run_levels(rep, todo, at_zero, write):
    compute = drinfeld_modular_polynomial_at_zero if at_zero else drinfeld_modular_polynomial
    what = "Phi_N(X,0)" if at_zero else "Phi_N(X,Y)"
    for N in todo:
        q = N.base_ring().cardinality()
        Phi, cert = compute(N, certificate=True)
        line = "   q = %d  N = %-22s psi = %2d  place %-13s K = %4d  E = F_q^%-3d %7.1fs" % (
            q, N, psi(N), cert["place"], cert["precision"], cert["extension_degree"],
            cert["seconds"])
        if write:
            save_polynomial(path(N, at_zero), Phi, N, record(cert))
            rep.say(line + "   written")
        else:
            ref, _ = load(N, at_zero)
            ok = rep.check("%s for q = %d, N = %s agrees with data/" % (what, q, N), Phi == ref)
            rep.say(line + ("   identical to data/" if ok else "   *** DIFFERS from data/"))


def run_places(rep, slow):
    r"""Proposition 5.1: the output does not depend on the choices made."""
    A2, A3, A4, A9 = ring(2), ring(3), ring(2, 2), ring(3, 2)
    T2, T3, T4, T9 = A2.gen(), A3.gen(), A4.gen(), A9.gen()
    y4, y9 = A4.base_ring().gen(), A9.base_ring().gen()
    tests = [
        (T2, [T2 + 1, T2**2 + T2 + 1, T2**3 + T2 + 1, T2**3 + T2**2 + 1]),
        (T2**2 + T2 + 1, [T2, T2 + 1, T2**3 + T2 + 1]),
        (T2**2 + T2, [T2**2 + T2 + 1, T2**3 + T2 + 1]),
        (T3 + 1, [T3, T3 + 2, T3**2 + 1, T3**3 + 2*T3 + 1]),
        (T3**2 + 1, [T3, T3 + 1]),
        (T4, [T4 + 1, T4 + y4]),
    ]
    if slow:
        tests.append((T9, [T9 + 1, T9 + y9]))
    # Section 5.1: for q = 9 the fields E at the places T + 1 and T + y are
    # F_(3^8) and F_(3^16)
    expected_E = {T9 + 1: 8, T9 + y9: 16}
    for N, places in tests:
        Fq = N.base_ring()
        q = Fq.cardinality()
        ref, _ = load(N)
        for P in places:
            for root_index in ((0, 1) if P.degree() > 1 else (0,)):
                Phi, cert = drinfeld_modular_polynomial(N, place=P, root_index=root_index,
                                                        certificate=True)
                degE = cert["extension_degree"] * Fq.degree()
                ok = rep.check("q = %d, N = %s at the place %s" % (q, N, P), Phi == ref)
                if P.parent() is A9:
                    rep.check("q = 9, place %s: E = F_(3^%d)" % (P, expected_E[P]),
                              degE == expected_E[P])
                rep.say("   q = %d  N = %-12s place %-14s (deg %d, root %d)  E = F_%d^%-3d %6.1fs   %s"
                        % (q, N, P, P.degree(), root_index, Fq.characteristic(), degE,
                           cert["seconds"], "identical" if ok else "*** DIFFERS"))


def main(args):
    write = "--write" in args
    modes = [a for a in args if not a.startswith("--")] or ["quick"]
    rep = Report()
    t0 = time.time()
    for mode in modes:
        if mode in ("quick", "all"):
            todo = levels()
            if mode == "quick":
                todo = [N for N in todo if psi(N) <= 6]
            rep.section("Phi_N(X,Y), recomputed with the proven height bound"
                        + ("" if write else ", compared with data/"))
            run_levels(rep, todo, False, write)
        if mode in ("zero", "all"):
            rep.section("Phi_N(X,0) for all monic N of degree 3 and 4 over F_2")
            run_levels(rep, levels_at_zero(), True, write)
        if mode in ("places", "places-all"):
            rep.section("Independence of the base place and of the chosen root of P")
            run_places(rep, slow=(mode == "places-all"))
    rep.say()
    rep.say("total time %.0fs" % (time.time() - t0))
    return rep.finish()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
