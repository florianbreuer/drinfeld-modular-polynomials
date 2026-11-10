# -*- coding: utf-8 -*-
r"""
Self-tests of the package ``drinfeld_modpoly`` (about a minute).

    sage tests/run_tests.py

These tests do not use the files in ``data/``: everything is computed from
scratch and compared with independent information (the closed form of
Bassa--Beelen, Kronecker congruences, a second base place, ...).
"""
from __future__ import print_function

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sage.all import GF, PolynomialRing, ZZ, QQ, Infinity

from drinfeld_modpoly import (drinfeld_modular_polynomial,
                              drinfeld_modular_polynomial_at_zero, psi, height,
                              height_bound, choose_place, monic_primes,
                              ReducedDrinfeldModule, reduced_module_with_j,
                              is_supersingular, supersingular_j_invariants)
from drinfeld_modpoly.modular_polynomial import TruncatedSeriesRing
from drinfeld_modpoly.analysis import (is_monic, is_symmetric, kronecker_congruence,
                                       shifted, specialization, C_J, n_opt, bound_holds,
                                       newton_root_valuations, apply_automorphism)
from drinfeld_modpoly.special import (bassa_beelen_phi_T, conductor_singular_modulus,
                                      sqrtT_singular_modulus)
from drinfeld_modpoly.database import save_polynomial, load_polynomial

FAILED = []


def test(fn):
    t0 = time.time()
    try:
        fn()
        print("ok    %-52s %5.1fs" % (fn.__name__, time.time() - t0))
    except Exception as exc:                    # report and carry on
        FAILED.append(fn.__name__)
        print("FAIL  %-52s %s: %s" % (fn.__name__, type(exc).__name__, exc))
    sys.stdout.flush()


def ring(q):
    return PolynomialRing(GF(q, 'y') if not ZZ(q).is_prime() else GF(q), 'T')


def test_series_ring():
    # the two implementations of Frobenius agree; inverse and power are right
    for q, M in ((2, 6), (3, 4), (4, 3), (9, 2)):
        p = ZZ(q).factor()[0][0]
        E = GF(p ** (M * ZZ(q).valuation(p)), 'z')
        R = TruncatedSeriesRing(E, 60, q)
        f = R.S([E.random_element() for _ in range(60)])
        f = f + (1 - f[0])                                   # a unit
        for n in (1, 2):
            Q = q ** n
            g = f.truncate(-(-60 // Q))
            slow = R.S(dict((Q * k, c ** Q) for k, c in enumerate(g.list()) if c))
            assert R.frobenius(f, n) == slow == (f ** Q).truncate(60)
        assert R.mul(f, R.inverse(f)) == 1
        assert R.power(f, 7) == (f ** 7).truncate(60)


def test_level_T_against_bassa_beelen():
    for q in (2, 3, 4, 5):
        A = ring(q)
        Phi = drinfeld_modular_polynomial(A.gen())
        assert Phi == bassa_beelen_phi_T(A)
        assert height(Phi) == q ** 2 * (q + 1)
        assert is_monic(Phi) and is_symmetric(Phi)
        assert kronecker_congruence(Phi, A.gen())


def test_independence_of_choices():
    A = ring(2)
    T = A.gen()
    N = T ** 2 + T + 1
    Phi = drinfeld_modular_polynomial(N)
    assert kronecker_congruence(Phi, N)
    for P in (T, T + 1, T ** 3 + T + 1):
        for r in (0, 1, 2)[:P.degree()]:
            assert drinfeld_modular_polynomial(N, place=P, root_index=r) == Phi
    assert drinfeld_modular_polynomial(N, extra_digits=3) == Phi
    A = ring(4)
    T, y = A.gen(), A.base_ring().gen()
    Phi = drinfeld_modular_polynomial(T)
    assert drinfeld_modular_polynomial(T, place=T + y, root_index=1) == Phi
    assert drinfeld_modular_polynomial(T, place=T ** 2 + T + y) == Phi


def test_composite_and_nonsquarefree_levels():
    A = ring(2)
    T = A.gen()
    assert choose_place(T ** 2 + T).degree() == 2
    PT, PT1 = drinfeld_modular_polynomial(T), drinfeld_modular_polynomial(T + 1)
    PTT1, cert = drinfeld_modular_polynomial(T ** 2 + T, certificate=True)
    assert cert["place"] == T ** 2 + T + 1 and cert["psi"] == 9
    # Res_Z(Phi_T(X,Z), Phi_(T+1)(Z,Y)) = Phi_(T(T+1))(X,Y)
    R4 = PolynomialRing(GF(2), 'T,X,Y,Z')
    t, x, y, z = R4.gens()
    flat = lambda Phi, u, v: sum(c(t) * u ** k[0] * v ** k[1] for k, c in Phi.dict().items())
    assert flat(PT, x, z).resultant(flat(PT1, z, y), z) == flat(PTT1, x, y)
    # sigma : T -> T + 1 swaps Phi_T and Phi_(T+1) and fixes Phi_(T(T+1))
    assert apply_automorphism(PT, 1, 1) == PT1
    assert apply_automorphism(PTT1, 1, 1) == PTT1
    PT2 = drinfeld_modular_polynomial(T ** 2)
    assert psi(T ** 2) == 6 and is_monic(PT2) and is_symmetric(PT2) and height(PT2) == 24


def test_specialization_at_zero():
    A = ring(3)
    T = A.gen()
    for N in (T, T + 1, T ** 2 + 1):
        f = drinfeld_modular_polynomial_at_zero(N)
        assert f.degree() == psi(N) and f.is_monic()
        if N.degree() == 1:
            assert f.list() == specialization(drinfeld_modular_polynomial(N), 0, 0)
    x = PolynomialRing(A, 'x').gen()
    Jc = conductor_singular_modulus(A)
    assert drinfeld_modular_polynomial_at_zero(T).list() == ((x - Jc) ** 4).list()
    A = ring(2)
    T = A.gen()
    f = drinfeld_modular_polynomial_at_zero(T ** 3 + T + 1)
    assert newton_root_valuations(f, T + 1) == {3: 6, 6: 3}
    assert f == drinfeld_modular_polynomial_at_zero(T ** 3 + T + 1, place=T ** 2 + T + 1)


def test_theorem_1_2_small_cases():
    for q, coeffs in ((2, [1, 1, 1]), (3, [1, 1]), (4, [0, 1])):
        A = ring(q)
        N = A(coeffs)
        Phi = drinfeld_modular_polynomial(N)
        for P in monic_primes(A, 1):
            if P.divides(N):
                continue
            assert C_J(Phi, 0, 0, P) == psi(N)
            assert bound_holds(Phi, P, psi(N), q + 1)
            assert n_opt(Phi, P, psi(N))[0] == q + 1


def test_theorem_4_1_small_cases():
    A = ring(3)
    T = A.gen()
    Phi = drinfeld_modular_polynomial(T + 1)
    X, Y = Phi.parent().gens()
    for J, const in ((T, QQ(5) / 4), (T ** 2, QQ(5) / 2), (T ** 3, QQ(13) / 4),
                     (sqrtT_singular_modulus(A), QQ(5) / 2),
                     (conductor_singular_modulus(A), QQ(5) / 4)):
        S = shifted(Phi, J)
        assert S == Phi(X + J, Y + J)
        assert C_J(Phi, J, J, T) == 4
        assert bound_holds(S, T, 4, const) and n_opt(S, T, 4)[0] == const


def test_reduction():
    A = ring(2)
    T = A.gen()
    M = ReducedDrinfeldModule(T ** 3 + T + 1, T + 1)
    assert len(M.kernels) == 9
    assert sum(1 for C in M.kernels if M.S(C) == 0) == 3
    assert all(M.quotient(C)[0] == M.quotient_bottom(C) for C in M.kernels)
    # a place of degree 3: theta_P does not commute with tau^2
    N, P = T ** 3, T ** 3 + T ** 2 + 1
    M = ReducedDrinfeldModule(N, P)
    assert M.count_isogenous(0) == 3
    assert M.count_isogenous(0) == sum(
        1 for c in drinfeld_modular_polynomial_at_zero(N).list()[:3] if c % P == 0)
    # residue-level count against the modular polynomial, for a general j
    A = ring(3)
    T = A.gen()
    N = T + 1
    Phi = drinfeld_modular_polynomial(N)
    for P in (T, T + 2, T ** 2 + 1, T ** 2 + T + 2):
        for J in (A(0), A(1), T, T + 2, T ** 2 + 1):
            assert reduced_module_with_j(N, P, J).count_isogenous(J) == C_J(Phi, J, J, P)
            for J1 in (A(0), A(1), T):
                assert reduced_module_with_j(N, P, J).count_isogenous(J1) == C_J(Phi, J1, J, P)
    assert supersingular_j_invariants(T ** 2 + T + 2) == [T + 2]
    assert [is_supersingular(P) for P in (T, T ** 2 + 1, T ** 3 + 2 * T + 1)] == [True, False, True]


def test_database_roundtrip():
    import tempfile
    for q in (2, 4):
        A = ring(q)
        T = A.gen()
        N = T + 1 if q == 2 else T + A.base_ring().gen()
        Phi = drinfeld_modular_polynomial(N)
        f = drinfeld_modular_polynomial_at_zero(N)
        d = tempfile.mkdtemp()
        for obj, name in ((Phi, "a.json"), (f, "b.json")):
            save_polynomial(os.path.join(d, name), obj, N)
            back, N0, rec = load_polynomial(os.path.join(d, name))
            assert N0 == N and back == obj and rec["psi"] == psi(N)


def test_display():
    from drinfeld_modpoly.display import CoefficientTable, Table, factored
    A = ring(3)
    T = A.gen()
    assert factored(2 * T ** 2 * (T + 1) ** 3 * (T ** 2 + 1)) == "2 * T^2 * (T + 1)^3 * (T^2 + 1)"
    assert factored(T ** 2 + 1) == "T^2 + 1" and factored(T ** 2 + 1, bare=False) == "(T^2 + 1)"
    Phi = drinfeld_modular_polynomial(T + 1)
    tab = CoefficientTable(Phi, bounds={P: (4, 4) for P in (T, T + 2)})
    # Phi_(T+1)(X,0) = (X - J)^4 with J = -(T+1) T^4 (T+2)^4, so a_(0,0) = J^4
    assert repr(tab).splitlines()[0] == "a_(0,0) = [T^16 * (T + 2)^16] * (T + 1)^4"
    assert tab._repr_latex_().startswith("$$") and r"\mathbf{T^{16} (T + 2)^{16}}" in tab._repr_latex_()
    try:                                        # a bound that does not hold is refused
        CoefficientTable(Phi, bounds={T: (4, 5)})
    except ValueError:
        pass
    else:
        raise AssertionError("a false bound was accepted")
    t = Table([[2, T + 1, 3]], header=["q", "N", "psi"])
    assert repr(t).splitlines()[-1] == "2  T + 1  3" and "<td" in t._repr_html_()


def test_input_validation():
    A = ring(3)
    T = A.gen()
    for bad in (lambda: drinfeld_modular_polynomial(2 * T),
                lambda: drinfeld_modular_polynomial(A(1)),
                lambda: drinfeld_modular_polynomial(T, place=T),
                lambda: drinfeld_modular_polynomial(T, place=T ** 2 + 2),
                lambda: drinfeld_modular_polynomial(T, h=5)):
        try:
            bad()
        except (ValueError, TypeError, ArithmeticError):
            continue
        raise AssertionError("invalid input was accepted")


if __name__ == "__main__":
    t0 = time.time()
    for fn in (test_series_ring, test_level_T_against_bassa_beelen,
               test_independence_of_choices, test_composite_and_nonsquarefree_levels,
               test_specialization_at_zero, test_theorem_1_2_small_cases,
               test_theorem_4_1_small_cases, test_reduction, test_database_roundtrip,
               test_display, test_input_validation):
        test(fn)
    print("%s  (%.0fs)" % ("ALL TESTS PASSED" if not FAILED else
                          "FAILED: " + ", ".join(FAILED), time.time() - t0))
    sys.exit(1 if FAILED else 0)
