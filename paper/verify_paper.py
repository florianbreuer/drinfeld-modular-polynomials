# -*- coding: utf-8 -*-
r"""
Verify the numerical claims of

    F. Breuer, F. Pazuki, "Divisibility of the coefficients of Drinfeld
    modular polynomials"

from the certified modular polynomials stored in ``data/``.

    sage paper/verify_paper.py              # everything (a few minutes)
    sage paper/verify_paper.py A C          # only the sections named
    sage paper/verify_paper.py --log FILE   # also write the report to FILE

Sections:

    A  the data set: monic, symmetric, Kronecker congruences, heights,
       compatibility with the automorphisms of F_q[T]          (Sections 5, 5.1)
    B  Table 1: the factored coefficients of Phi_{T^2+T+1}, q = 2  (Section 5.2)
    C  primes of degree one: Theorem 1.2(1) and its optimality     (Section 5.3)
    D  primes of degree two and three: Theorem 1.2(2)              (Section 5.4)
    E  ramified and singular moduli: Theorem 4.1, Corollaries 4.3
       and 4.6, Propositions 2.4 and 4.5                     (Sections 4 and 5.5)
    F  external checks: Bassa--Beelen, Caranay--Greenberg--Scheidler,
       the resultant identity for Phi_{T(T+1)}                     (Section 5.1)

To recompute the polynomials themselves, see ``recompute.py``.
(Theorem, section and table numbers are those of the version of the paper of
November 2026.)
"""
from __future__ import print_function

import sys
import time

from cases import levels_at_zero, load, ring, Dataset, Report

from sage.all import ZZ, QQ, GF, PolynomialRing, Infinity, gcd, set_random_seed

from drinfeld_modpoly import (psi, height_bound, b_q, B_q, height, monic_primes,
                              valuation, ReducedDrinfeldModule,
                              reduced_module_with_j, is_supersingular,
                              supersingular_j_invariants)
from drinfeld_modpoly.analysis import (coefficient_dict, is_symmetric, is_monic,
                                       shifted, specialization, C_J, n_opt,
                                       bound_holds, vanishes_below,
                                       kronecker_congruence, newton_root_valuations,
                                       apply_automorphism)
from drinfeld_modpoly.special import (sqrtT_singular_modulus,
                                      conductor_singular_modulus, bassa_beelen_phi_T)


def tag(N):
    return "q = %d, N = %s" % (N.base_ring().cardinality(), N)


def order_mod(coeffs, P=None):
    r"""ord_X of sum coeffs[i] X^i, modulo P if P is given."""
    c = 0
    for a in coeffs:
        if (a if P is None else a % P) != 0:
            break
        c += 1
    return c


def primes_not_dividing(N, d):
    return [P for P in monic_primes(N.parent(), d) if not P.divides(N)]


# ---------------------------------------------------------------------- A

def section_A(rep, data):
    rep.section("A. The data set: Phi_N(X,Y) for 20 levels (Sections 5 and 5.1)")
    ratios = []
    for N, Phi, rec in data:
        A = N.parent()
        Fq = A.base_ring()
        q, p, ps = ZZ(Fq.cardinality()), Fq.characteristic(), psi(N)
        X, Y = Phi.parent().gens()
        rep.check(tag(N) + ": degree psi(N) in X and in Y",
                  Phi.degree(X) == ps and Phi.degree(Y) == ps)
        rep.check(tag(N) + ": monic", is_monic(Phi))
        rep.check(tag(N) + ": symmetric", is_symmetric(Phi))
        notes = ""
        if N.is_irreducible():
            rep.check(tag(N) + ": Kronecker congruence", kronecker_congruence(Phi, N))
            notes += "  Kronecker ok"
        h, hb = height(Phi), height_bound(N)
        b = b_q(N, h)
        rep.check(tag(N) + ": height below the proven bound", h <= hb)
        rep.check(tag(N) + ": 0 <= b_q(N) <= B_q", 0 <= b <= B_q(q))
        if N.degree() == 1:
            rep.check(tag(N) + ": height q^2(q+1) at level of degree 1", h == q ** 2 * (q + 1))
            notes += "  h = q^2(q+1)"
        if Fq.degree() > 1:
            rep.check(tag(N) + ": coefficients in F_p[T]",
                      all(c ** p == c for a in Phi.coefficients() for c in a.list()))
        ratios.append((QQ(hb) / h, tag(N)))
        rep.say("   q = %d  N = %-14s psi = %2d  height %4d <= bound %4d  b_q(N) = %.3f <= B_q = %.3f%s"
                % (q, N, ps, h, hb, float(b), float(B_q(q)), notes))
    lo, hi = min(ratios), max(ratios)
    rep.say("   proven bound / true height: min %.2f (%s), max %.2f (%s)"
            % (float(lo[0]), lo[1], float(hi[0]), hi[1]))
    rep.check("the bound exceeds the height by a factor between 2.8 and 7.4",
              abs(float(lo[0]) - 2.8) < 0.05 and abs(float(hi[0]) - 7.4) < 0.05)
    N0, Phi0, _ = data[0]
    rep.check("q = 2, level T: h = 57 and h(Phi_T) = 12",
              N0 == N0.parent().gen() and height_bound(N0) == 57 and height(Phi0) == 12)

    # sigma(Phi_N) = Phi_sigma(N) for the automorphisms sigma : T -> aT + b of A
    count = 0
    for N, Phi, _ in data:
        A = N.parent()
        T, Fq = A.gen(), A.base_ring()
        for a in Fq:
            for b in Fq:
                if a == 0 or (a == 1 and b == 0):
                    continue
                sN = N(a * T + b).monic()
                if data.has(sN):
                    count += 1
                    rep.check("%s: Phi_sigma(N) = a^(-psi) sigma(Phi_N)(aX, aY) for sigma(T) = (%s)T + (%s)"
                              % (tag(N), a, b), apply_automorphism(Phi, a, b) == data.phi(sN))
    rep.say("   Phi_sigma(N)(X,Y) = a^(-psi) sigma(Phi_N)(aX, aY) verified for %d pairs (N, sigma), "
            "sigma(T) = aT + b" % count)


# ---------------------------------------------------------------------- B

# Table 1 of the paper: (m, n) -> list of (factor, exponent); factors as
# coefficient lists, constant term first.
TABLE1 = {
    (2, 0): [([0, 1], 9), ([1, 1], 9), ([1, 1, 1], 3)],
    (1, 1): [([0, 1], 11), ([1, 1], 11)],
    (3, 0): [([0, 1], 6), ([1, 1], 6), ([1, 1, 1], 2)],
    (2, 1): [([0, 1], 6), ([1, 1], 6), ([1, 1, 1], 1), ([1, 1, 0, 0, 1], 1)],
    (4, 0): [([0, 1], 3), ([1, 1], 3), ([1, 1, 1], 1)],
    (3, 1): [([0, 1], 3), ([1, 1], 3), ([1, 1, 1], 1)],
    (2, 2): [([0, 1], 5), ([1, 1], 5), ([1, 1, 1], 1), ([1, 1, 0, 0, 1], 1)],
    (5, 0): [],
    (4, 1): [([1, 1, 1], 1)],
    (4, 2): [([1, 1, 1], 1)],
    (3, 2): [([0, 1], 1), ([1, 1], 1), ([1, 1, 1], 1), ([1, 0, 1, 1], 1), ([1, 1, 0, 1], 1)],
    (3, 3): [([0, 1], 2), ([1, 1], 2), ([1, 1, 1], 1)],
    (4, 4): [],
}
TABLE1_ZERO = [(0, 0), (1, 0), (5, 1), (5, 2), (4, 3), (5, 3), (5, 4), (5, 5)]


def section_B(rep, data):
    rep.section("B. Table 1: the coefficients of Phi_{T^2+T+1} for q = 2 (Section 5.2)")
    A = ring(2)
    T = A.gen()
    N = T ** 2 + T + 1
    Phi = data.phi(N)
    d = coefficient_dict(Phi)
    ps = psi(N)
    rep.check("psi(N) = 5 and C_0(N,0) = 2", ps == 5 and C_J(Phi) == 2)
    for m in range(ps + 1):
        for n in range(m + 1):
            a = d.get((m, n), A.zero())
            if a == 0:
                ok = (m, n) in TABLE1_ZERO
                txt = "0"
            else:
                ok = (m, n) in TABLE1 and a == A.prod(A(f) ** k for f, k in TABLE1[(m, n)])
                txt = str(a.factor())
            rep.check("Table 1, a_(%d,%d)" % (m, n), ok)
            rep.say("   a_(%d,%d) = %s" % (m, n, txt))
    # the predicted factor (T(T+1))^(3(5-m-n)) is attained exactly at a_(2,0)
    rep.check("v_T(a_(2,0)) = v_(T+1)(a_(2,0)) = 9 = 3(5 - 2)",
              valuation(d[(2, 0)], T) == 9 and valuation(d[(2, 0)], T + 1) == 9)


# ---------------------------------------------------------------------- C

def section_C(rep, data):
    rep.section("C. Primes of degree one: Theorem 1.2(1) and optimality of q+1 (Section 5.3)")
    pairs, by_q, not_low = 0, {}, []
    for N, Phi, _ in data:
        A = N.parent()
        q, ps = ZZ(A.base_ring().cardinality()), psi(N)
        c0 = C_J(Phi)                                   # C_0(N,0)
        d = coefficient_dict(Phi)
        f0 = specialization(Phi, 0, 0)                  # Phi_N(X,0)
        for P in primes_not_dividing(N, 1):
            lab = "%s, P = %s" % (tag(N), P)
            C = C_J(Phi, 0, 0, P)
            nopt, where = n_opt(Phi, P, C)
            rep.check(lab + ": C_0(N,P) = psi(N)  (Proposition 2.3)", C == ps)
            rep.check(lab + ": v_P(a_mn) >= (q+1)(psi - m - n)  (Theorem 1.2(1))",
                      bound_holds(Phi, P, ps, q + 1))
            rep.check(lab + ": n_opt = q + 1", nopt == q + 1)
            at_low = (c0, 0) in where
            if not at_low:
                not_low.append((q, N, P, valuation(d[(c0, 0)], P)))

            # the same pair at the residue level (no height bound involved)
            M = ReducedDrinfeldModule(N, P)
            rep.check(lab + ": psi(N) cyclic kernels, all with j(phi^0/C) = 0 mod P",
                      len(M.kernels) == ps and all(j == 0 for j in M.isogenous_j_invariants()))
            rep.check(lab + ": kernel polynomials have coefficients in F_(q^2)  (Lemma 3.7)",
                      all(c ** (q * q) == c for K in M.kernels for c in M.kernel_polynomial(K)))
            rep.check(lab + ": the two formulas for g' agree",
                      all(M.quotient(K)[0] == M.quotient_bottom(K) for K in M.kernels))
            zeros = sum(1 for K in M.kernels if M.S(K) == 0)
            # v_P(j(phi^0/C)) = (q+1)(1 + v_P(S_C)): compare with the Newton polygon
            nv = newton_root_valuations(f0, P)
            rep.check(lab + ": root valuations of Phi_N(X,0) match the residues S_C",
                      nv.get(Infinity, 0) == c0 and nv.get(q + 1, 0) == ps - zeros
                      and all(v == Infinity or (v in ZZ and v % (q + 1) == 0) for v in nv))
            rep.check(lab + ": n_opt attained at a_(C_0(N,0),0) iff no kernel has P | S_C",
                      at_low == (zeros == c0))
            pairs += 1
            by_q[q] = by_q.get(q, 0) + 1
            rep.say("   q = %d  N = %-14s P = %-9s C_0 = %2d  n_opt = %s  kernels with P | S_C: %d of %d%s"
                    % (q, N, P, C, nopt, zeros - c0, ps - c0,
                       "" if at_low else "   <-- minimum not attained at a_(%d,0)" % c0))
    rep.say("   %d pairs (N,P); by q: %s" % (pairs, sorted(by_q.items())))
    rep.check("44 pairs (N,P) with deg P = 1, P not dividing N",
              pairs == 44 and by_q == {2: 8, 3: 21, 4: 3, 5: 4, 9: 8})
    A = ring(2)
    T = A.gen()
    rep.check("n_opt is attained at the lowest coefficient in 42 of the 44 cases; the exceptions "
              "are (2, T^3+T+1, T+1) with v_P(a_00) = 36 and (2, T^3, T+1) with v_P(a_00) = 54",
              sorted(not_low) == sorted([(2, T ** 3 + T + 1, T + 1, 36), (2, T ** 3, T + 1, 54)]))
    for N, total, zero in ((T ** 3 + T + 1, 9, 3), (T ** 3, 12, 6)):
        M = ReducedDrinfeldModule(N, T + 1)
        rep.check("q = 2, N = %s, P = T + 1: %d of the %d kernels have P | S_C" % (N, zero, total),
                  len(M.kernels) == total and sum(1 for K in M.kernels if M.S(K) == 0) == zero)


# ---------------------------------------------------------------------- D

def section_D(rep, data):
    rep.section("D. Primes of degree two and three (Section 5.4)")
    rep.say("   D1. the 20 full polynomials")
    excess = []
    for N, Phi, _ in data:
        A = N.parent()
        q = ZZ(A.base_ring().cardinality())
        c0 = C_J(Phi)
        f0 = specialization(Phi, 0, 0)
        rep.check(tag(N) + ": a_mn = 0 for m + n < C_0(N,0)  (Remark 3.9)",
                  vanishes_below(Phi, c0))
        P2 = primes_not_dividing(N, 2)
        rep.check(tag(N) + ": C_0(N,P) = C_0(N,0) at all primes of degree 2  (Proposition 2.6)",
                  all(order_mod(f0, P) == c0 for P in P2))
        P3 = primes_not_dividing(N, 3)
        here = []
        for P in P3:
            C = order_mod(f0, P)
            if C > c0:
                here.append((P, C))
                rep.check("%s, P = %s: Theorem 1.2(2)" % (tag(N), P), bound_holds(Phi, P, C, q + 1))
                rep.check("%s, P = %s: (q+1) | C_0(N,P) - C_0(N,0)" % (tag(N), P),
                          (C - c0) % (q + 1) == 0)
                rep.check("%s, P = %s: excess forces deg P <= deg N" % (tag(N), P),
                          P.degree() <= N.degree())
                excess.append((q, N, P, C, n_opt(Phi, P, C)[0]))
        rep.say("   q = %d  N = %-14s C_0(N,0) = %d;  %2d primes of degree 2: no excess;  %3d primes of degree 3: %s"
                % (q, N, c0, len(P2), len(P3),
                   ", ".join("C_0(N, %s) = %d" % pc for pc in here) or "no excess"))
    A = ring(2)
    T = A.gen()
    rep.check("the only excess among the 20 levels: C_0(T^3, T^3+T^2+1) = 3 for q = 2, with n_opt = 3",
              excess == [(2, T ** 3, T ** 3 + T ** 2 + 1, 3, 3)])
    rep.check("supersingularity of j = 0: exactly at the primes of odd degree (deg P <= 4, q = 2, 3)",
              all(is_supersingular(P) == (d % 2 == 1)
                  for p in (2, 3) for d in (1, 2, 3, 4) for P in monic_primes(ring(p), d)))

    rep.say("   D2. Phi_N(X,0) for the 24 monic N of degree 3 and 4 over F_2")
    table, c00, no_excess, recounts = {}, {}, [], 0
    for N in levels_at_zero():
        f, rec = load(N, at_zero=True)
        ps, co = psi(N), f.list()
        rep.check("N = %s: Phi_N(X,0) is monic of degree psi(N)" % N,
                  f.degree() == ps and f.leading_coefficient() == 1)
        if data.has(N):
            rep.check("N = %s: agrees with the full Phi_N(X,Y) at Y = 0" % N,
                      co == specialization(data.phi(N), 0, 0))
        place = A(rec["computation"]["place"])
        if (T * (T + 1)).divides(N):
            rep.check("N = %s (divisible by T(T+1)): computed at a place of degree 2 or 3" % N,
                      place.degree() in (2, 3))
        c0 = c00[N] = order_mod(co)
        found = []
        for d in (1, 2, 3):
            for P in primes_not_dividing(N, d):
                C = table[(N, P)] = order_mod(co, P)
                if d == 1:
                    rep.check("N = %s, P = %s: C_0(N,P) = psi(N)" % (N, P), C == ps)
                elif d == 2:
                    rep.check("N = %s, P = %s: C_0(N,P) = C_0(N,0)" % (N, P), C == c0)
                else:
                    rep.check("N = %s, P = %s: C_0(N,P) - C_0(N,0) is a multiple of q+1 = 3"
                              % (N, P), C >= c0 and (C - c0) % 3 == 0)
                    recount = ReducedDrinfeldModule(N, P).count_isogenous(0)
                    rep.check("N = %s, P = %s: residue-level recount of C_0(N,P)" % (N, P),
                              recount == C)
                    recounts += 1
                    if C > c0:
                        found.append("C_0(N, %s) = %d" % (P, C))
        if not found:
            no_excess.append(N)
        rep.say("   N = %-22s psi = %2d  C_0(N,0) = %d  %s"
                % (N, ps, c0, ", ".join(found) or "no excess at degree 3"))
    rep.check("20 of the 24 levels have excess at a prime of degree 3", len(no_excess) == 4)
    rep.check("the levels without excess: T^3+T+1, T^3+T^2+1, T^4+T+1, (T^2+T+1)^2",
              sorted(no_excess) == sorted([T ** 3 + T + 1, T ** 3 + T ** 2 + 1, T ** 4 + T + 1,
                                           (T ** 2 + T + 1) ** 2]))
    P31, P32 = T ** 3 + T + 1, T ** 3 + T ** 2 + 1
    named = [(T ** 3, P32, 3, 0), (T ** 4, P31, 6, 0), (T ** 4 + T ** 3 + 1, P32, 5, 2),
             (T ** 4 + T ** 3, P32, 9, 0)]
    for N, P, C, c0 in named:
        rep.check("C_0(%s, %s) = %d and C_0(N,0) = %d" % (N, P, C, c0),
                  table[(N, P)] == C and c00[N] == c0)
    rep.check("42 residue-level recounts at primes of degree 3", recounts == 42)
    f0 = specialization(data.phi(T ** 2 + T), 0, 0)
    rep.check("q = 2, N = T(T+1): C_0(N,P) = 0 at both primes of degree 3",
              order_mod(f0, P31) == 0 and order_mod(f0, P32) == 0)


# ---------------------------------------------------------------------- E

def section_E(rep, data):
    rep.section("E. Ramified and singular moduli (Sections 4 and 5.5)")

    rep.say("   E0. closed forms")
    for p, e in ((3, 1), (5, 1), (3, 2)):
        A = ring(p, e)
        T, Fq = A.gen(), A.base_ring()
        q = ZZ(Fq.cardinality())
        Js = sqrtT_singular_modulus(A)
        s = PolynomialRing(Fq, 's').gen()
        rep.check("q = %d: J_s = (s + s^q)^(q+1) with s^2 = T" % q,
                  Js(s ** 2) == (s + s ** q) ** (q + 1))
        rep.check("q = %d: v_T(J_s) = (q+1)/2; v_(T-theta)(J_s) = q+1 (theta a non-square), "
                  "0 (theta a nonzero square)" % q,
                  valuation(Js, T) == (q + 1) // 2
                  and all(valuation(Js, T - th) == (0 if th.is_square() else q + 1)
                          for th in Fq if th != 0))
    for N, Phi, _ in data:
        A = N.parent()
        T, Fq = A.gen(), A.base_ring()
        if N != T:
            continue
        q = ZZ(Fq.cardinality())
        Jc = conductor_singular_modulus(A)
        x = PolynomialRing(A, 'x').gen()
        rep.check("q = %d: Phi_T(X,0) = (X - J_c)^(q+1)  (Proposition 4.5(1))" % q,
                  specialization(Phi, 0, 0) == ((x - Jc) ** (q + 1)).list())
        rep.check("q = %d: v_T(J_c) = 1 and v_(T-theta)(J_c) = q+1  (Proposition 4.5(3))" % q,
                  valuation(Jc, T) == 1
                  and all(valuation(Jc, T - th) == q + 1 for th in Fq if th != 0))
        # Remark 4.4: the threshold q+1 is sharp: j = T^(q+2) is (T-1)-isogenous
        # to j-invariants of valuation q+1
        PhiTm1 = apply_automorphism(Phi, 1, -1)           # Phi_(T-1)
        nv = newton_root_valuations(specialization(PhiTm1, 0, T ** (q + 2)), T)
        rep.check("q = %d: Phi_(T-1)(X, T^(q+2)) has a root of T-adic valuation q+1  (Remark 4.4)" % q,
                  nv.get(q + 1, 0) > 0)
        rep.say("   q = %d: J_c = %s;  root valuations of Phi_(T-1)(X, T^(q+2)) at T: %s"
                % (q, Jc.factor(), dict(nv)))
    for p, e in ((2, 1), (3, 1), (2, 2), (5, 1)):
        A = ring(p, e)
        q = ZZ(A.base_ring().cardinality())
        rep.check("q = %d: j = 0 is the only supersingular invariant at primes of degree 1" % q,
                  all(supersingular_j_invariants(P) == [0] for P in monic_primes(A, 1)))
        rep.check("q = %d: exactly one supersingular invariant j_P in F_P at each prime of "
                  "degree 2, and j_P != 0  (Proposition 2.4)" % q,
                  all(len(supersingular_j_invariants(P)) == 1
                      and supersingular_j_invariants(P) != [0] for P in monic_primes(A, 2)))
    A = ring(3)
    T = A.gen()
    Js = sqrtT_singular_modulus(A)
    rep.check("q = 3: j_P = T + 2 = J_s mod P for P = T^2 + T + 2  (Remark 2.5)",
              supersingular_j_invariants(T ** 2 + T + 2) == [T + 2] == [Js % (T ** 2 + T + 2)])
    rep.check("q = 3: J_s = j_P mod P for P = T^2 + 2T + 2, but not for P = T^2 + 1",
              supersingular_j_invariants(T ** 2 + 2 * T + 2) == [Js % (T ** 2 + 2 * T + 2)]
              and supersingular_j_invariants(T ** 2 + 1) != [Js % (T ** 2 + 1)])

    rep.say("   E1. J_s = T^2(1+T)^4, q = 3: the table of Section 5.5")
    half = QQ(1) / 2
    # P -> (C_J(N,P) is psi(N) or C_J(N,0), v_P(J_s), n_opt)
    expected = {T: ("psi", 2, 5 * half), T + 1: ("psi", 4, QQ(4)), T + 2: ("generic", 0, None),
                T ** 2 + T + 2: ("psi", 0, QQ(1)), T ** 2 + 2 * T + 2: ("psi", 0, QQ(1)),
                T ** 2 + 1: ("generic", 0, None)}
    lv = [N for N in data.over(A) if N != T]
    rep.check("nine levels N for J_s", len(lv) == 9)
    for N in lv:
        Phi, ps = data.phi(N), psi(N)
        S = shifted(Phi, Js)
        cJ0 = C_J(Phi, Js)
        rep.check("J_s, N = %s: a_mn = 0 for m + n < C_J(N,0)" % N, vanishes_below(S, cJ0))
        parts = []
        for P in primes_not_dividing(N, 1) + primes_not_dividing(N, 2):
            kind, v, n = expected[P]
            C = C_J(Phi, Js, Js, P)
            nopt = n_opt(S, P, C)[0]
            rep.check("J_s, N = %s, P = %s: v_P(J_s), C_J(N,P), bound and n_opt as in the table" % (N, P),
                      valuation(Js, P) == v and C == (ps if kind == "psi" else cJ0)
                      and nopt == n and (n is None or bound_holds(S, P, C, n)))
            rep.check("J_s, N = %s, P = %s: residue-level recount of C_J(N,P)" % (N, P),
                      reduced_module_with_j(N, P, Js).count_isogenous(Js) == C)
            parts.append("%s: C = %d, n_opt = %s" % (P, C, nopt))
        rep.say("   N = %-12s psi = %2d  C_J(N,0) = %d | %s" % (N, ps, cJ0, " | ".join(parts)))

    rep.say("   E2. Theorem 4.1 for j-invariants that are not singular moduli")
    pairs = 0
    for p, consts in ((2, [QQ(4) / 3, QQ(7) / 3]), (3, [QQ(5) / 4, QQ(5) / 2, QQ(13) / 4])):
        A = ring(p)
        T = A.gen()
        q = ZZ(p)
        Jlist = [T, T ** 2, T * (1 + T), T + T ** 4] if p == 2 else [T, T ** 2, T ** 3]
        lv = [N for N in data.over(A) if not T.divides(N)]
        rep.check("q = %d: %d levels with T not dividing N" % (q, 3 if p == 2 else 8),
                  len(lv) == (3 if p == 2 else 8))
        seen = set()
        for J in Jlist:
            v = valuation(J, T)
            e = (q + 1) // gcd(q + 1, v)
            const = v + QQ(1) / e
            seen.add(const)
            for N in lv:
                Phi, ps = data.phi(N), psi(N)
                S = shifted(Phi, J)
                C = C_J(Phi, J, J, T)
                nopt = n_opt(S, T, C)[0]
                lab = "q = %d, J = %s, N = %s" % (q, J, N)
                rep.check(lab + ": C_J(N,T) = psi(N)", C == ps)
                rep.check(lab + ": v_T(a_mn) >= (v + 1/e)(psi - m - n)  (Theorem 4.1)",
                          bound_holds(S, T, ps, const))
                rep.check(lab + ": the constant v + 1/e = %s is attained" % const, nopt == const)
                # Corollary 4.3: for J2 N-isogenous to J: v_T(J2) = v_T(J), v_T(J2 - J) >= v + 1/e
                rep.check(lab + ": v_T(J2) = v_T(J) for all N-isogenous J2  (Corollary 4.3)",
                          newton_root_valuations(specialization(Phi, 0, J), T) == {v: ps})
                vmin = min(newton_root_valuations(specialization(Phi, J, J), T))
                rep.check(lab + ": v_T(J2 - J) >= v + 1/e  (Corollary 4.3)", vmin >= const)
                pairs += 1
                rep.say("   q = %d  J = %-9s N = %-12s v + 1/e = %-4s n_opt = %-4s min v_T(J2 - J) = %s"
                        % (q, J, N, const, nopt, vmin))
        rep.check("q = %d: the constants v + 1/e are %s" % (q, consts), seen == set(consts))
        rep.check("q = %d: every nonzero residue class of v_T(J) modulo q+1 occurs" % q,
                  set(valuation(J, T) for J in Jlist) == set(range(1, q + 1)))
        # Corollary 4.3 with v_T(J1) = 0
        for N in lv:
            rep.check("q = %d, N = %s: v_T(J2) = 0 for all J2 N-isogenous to J1 = 1" % (q, N),
                      newton_root_valuations(specialization(data.phi(N), 0, 1), T) == {0: psi(N)})
    rep.check("36 pairs (J, N)", pairs == 36)

    rep.say("   E3. the conductor-T singular modulus J_c, q = 2, 3  (Corollary 4.6)")
    count = 0
    for p in (2, 3):
        A = ring(p)
        T = A.gen()
        q = ZZ(p)
        Jc = conductor_singular_modulus(A)
        for N in [N for N in data.over(A) if not T.divides(N)]:
            Phi, ps = data.phi(N), psi(N)
            S = shifted(Phi, Jc)
            cJ0 = C_J(Phi, Jc)
            rep.check("J_c, q = %d, N = %s: a_mn = 0 for m + n < C_J(N,0)" % (q, N),
                      vanishes_below(S, cJ0))
            parts = []
            for P in primes_not_dividing(N, 1) + primes_not_dividing(N, 2):
                C = C_J(Phi, Jc, Jc, P)
                nopt = n_opt(S, P, C)[0]
                if P.degree() == 1:
                    n = QQ(q + 2) / (q + 1) if P == T else QQ(q + 1)
                    ok = C == ps and nopt == n and bound_holds(S, P, C, n)
                else:
                    ok = C == cJ0 and cJ0 in (0, 2) and nopt is None
                rep.check("J_c, q = %d, N = %s, P = %s" % (q, N, P), ok)
                rep.check("J_c, q = %d, N = %s, P = %s: residue-level recount of C_J(N,P)" % (q, N, P),
                          reduced_module_with_j(N, P, Jc).count_isogenous(Jc) == C)
                parts.append("%s: C = %d, n_opt = %s" % (P, C, nopt))
            count += 1
            rep.say("   q = %d  N = %-12s psi = %2d  C_J(N,0) = %d | %s"
                    % (q, N, ps, cJ0, " | ".join(parts)))
    rep.check("11 levels for J_c", count == 11)


# ---------------------------------------------------------------------- F

def section_F(rep, data):
    rep.section("F. External checks (Section 5.1)")

    for N, Phi, _ in data:
        A = N.parent()
        if N == A.gen():
            q = A.base_ring().cardinality()
            ok = rep.check("q = %d: Phi_T equals the closed form of Bassa--Beelen" % q,
                           Phi == bassa_beelen_phi_T(A))
            rep.say("   q = %d: Phi_T = Bassa--Beelen closed form: %s" % (q, ok))

    # Caranay--Greenberg--Scheidler 2020, Example 6.2 (2) and (3): q = 3,
    # Phi_N(X, j) modulo T^5 + 2T + 1
    A = ring(3)
    T = A.gen()
    mod = T ** 5 + 2 * T + 1
    cgs = [(T + 1, T ** 2,
            [T ** 2, 2 * T ** 3 + 2 * T ** 2 + 2 * T + 1, 2 * T ** 4 + 2 * T ** 3 + 2 * T ** 2,
             2 * T ** 4 + T ** 3 + 2 * T + 1, 1]),
           (T + 2, T ** 4 + T ** 3 + T ** 2 + 2 * T + 2,
            [T ** 4 + T ** 2 + 2 * T, 2 * T ** 4 + T ** 3 + 2 * T ** 2 + T, 2 * T ** 4 + T + 2,
             T ** 4 + 2 * T ** 3 + 2 * T ** 2 + 1, 1])]
    for N, j, expected in cgs:
        ok = rep.check("CGS Example 6.2: Phi_(%s)(X, %s) mod %s" % (N, j, mod),
                       specialization(data.phi(N), 0, j, mod) == [A(c) for c in expected])
        rep.say("   Caranay--Greenberg--Scheidler, Example 6.2, N = %s: %s" % (N, ok))

    # Res_Z(Phi_T(X,Z), Phi_(T+1)(Z,Y)) = Phi_(T(T+1))(X,Y) for q = 2
    A = ring(2)
    T = A.gen()
    PT, PT1, PTT1 = data.phi(T), data.phi(T + 1), data.phi(T ** 2 + T)
    R4 = PolynomialRing(GF(2), 'T,X,Y,Z')
    t, x, y, z = R4.gens()
    flat = lambda Phi, u, v: sum(c(t) * u ** m * v ** n
                                 for (m, n), c in coefficient_dict(Phi).items())
    res = flat(PT, x, z).resultant(flat(PT1, z, y), z)
    ok = rep.check("q = 2: Res_Z(Phi_T(X,Z), Phi_(T+1)(Z,Y)) = Phi_(T(T+1))(X,Y) exactly",
                   res == flat(PTT1, x, y))
    rep.say("   resultant identity for Phi_(T(T+1)), q = 2, as polynomials in T, X, Y: %s" % ok)
    set_random_seed(20260825)
    K = GF(2 ** 12, 'c')
    S = PolynomialRing(K, 'Z')
    Zv = S.gen()
    ev = lambda Phi, u, v, t0: sum(c(t0) * u ** m * v ** n
                                   for (m, n), c in coefficient_dict(Phi).items())
    good = 0
    for _ in range(25):
        t0, x0, y0 = K.random_element(), K.random_element(), K.random_element()
        lhs = S(ev(PT, x0, Zv, t0)).resultant(S(ev(PT1, Zv, y0, t0)))
        good += int(lhs == ev(PTT1, x0, y0, t0))
    rep.check("the same identity at 25 random specializations over F_(2^12)", good == 25)
    rep.say("   ... and at %d of 25 random specializations (T, X, Y) in F_(2^12)" % good)


SECTIONS = [("A", section_A), ("B", section_B), ("C", section_C), ("D", section_D),
            ("E", section_E), ("F", section_F)]


def main(args):
    log = None
    if "--log" in args:
        i = args.index("--log")
        log = args[i + 1]
        args = args[:i] + args[i + 2:]
    wanted = [a.upper() for a in args] or [name for name, _ in SECTIONS]
    rep = Report(log)
    rep.say("Verification of the numerical claims of Breuer--Pazuki,")
    rep.say('"Divisibility of the coefficients of Drinfeld modular polynomials"')
    data = Dataset()
    rep.say("loaded %d modular polynomials from data/phi" % len(data))
    for name, fn in SECTIONS:
        if name in wanted:
            t0 = time.time()
            fn(rep, data)
            rep.say("   [section %s: %.0fs]" % (name, time.time() - t0))
    return rep.finish()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
