# -*- coding: utf-8 -*-
r"""
Divisibility statistics of the coefficients of `\Phi_N(X+J_1, Y+J_2)`.

Notation of the paper: for `J_1, J_2 \in A = \GF{q}[T]` write

.. MATH::

    \Phi_N(X + J_1, Y + J_2) = \sum_{m,n} a_{m,n} X^m Y^n, \qquad a_{m,n} \in A,

and for a monic prime `P \nmid N`

.. MATH::

    C_{J_1,J_2}(N,P) = \mathrm{ord}_X\bigl(\Phi_N(X + J_1, J_2) \bmod P\bigr),
    \qquad
    C_{J_1,J_2}(N,0) = \mathrm{ord}_X\,\Phi_N(X + J_1, J_2).

The theorems of the paper are lower bounds of the shape
`v_P(a_{m,n}) \ge c\,(C - m - n)`; the best constant for a given polynomial is

.. MATH::

    n_{\mathrm{opt}} = \min\Bigl\{\frac{v_P(a_{m,n})}{C - m - n} : m + n < C,\ a_{m,n} \ne 0\Bigr\}.
"""
from sage.all import ZZ, QQ, Infinity

from drinfeld_modpoly.util import valuation


def coefficient_dict(Phi):
    r"""
    The nonzero coefficients of `\Phi \in A[X,Y]` as a dictionary
    ``{(m, n): a_mn}``.
    """
    return dict(((ZZ(k[0]), ZZ(k[1])), c) for k, c in Phi.dict().items())


def is_symmetric(Phi):
    r"""Whether `\Phi(X,Y) = \Phi(Y,X)`."""
    d = coefficient_dict(Phi)
    return all(d.get((n, m)) == a for (m, n), a in d.items())


def is_monic(Phi):
    r"""Whether `\Phi \in A[X,Y]` is monic in `X` (leading coefficient `1 \in A[Y]`)."""
    d = coefficient_dict(Phi)
    top = max(m for m, _ in d)
    return [(m, n) for (m, n) in d if m == top] == [(top, 0)] and d[(top, 0)] == 1


def _taylor_shift(c, J):
    r"""Coefficients of `f(X + J)` from the coefficients ``c`` of `f(X)`."""
    c = list(c)
    n = len(c)
    for i in range(n - 1):
        for k in range(n - 2, i - 1, -1):
            c[k] = c[k] + J * c[k + 1]
    return c


def shifted(Phi, J1, J2=None):
    r"""
    Return `\Phi(X + J_1, Y + J_2)` (with `J_2 = J_1` by default), by binomial
    expansion (Taylor shifts).

    EXAMPLES::

        sage: from drinfeld_modpoly import drinfeld_modular_polynomial
        sage: from drinfeld_modpoly.analysis import shifted
        sage: A.<T> = GF(3)[]
        sage: Phi = drinfeld_modular_polynomial(T + 1)
        sage: X, Y = Phi.parent().gens()
        sage: shifted(Phi, T^2, T) == Phi(X + T^2, Y + T)
        True
    """
    R = Phi.parent()
    A = R.base_ring()
    J1 = A(J1)
    J2 = J1 if J2 is None else A(J2)
    d = coefficient_dict(Phi)
    dx = max(m for m, _ in d) + 1
    dy = max(n for _, n in d) + 1
    a = [[d.get((m, n), A.zero()) for n in range(dy)] for m in range(dx)]
    if J1:
        for n in range(dy):
            col = _taylor_shift([a[m][n] for m in range(dx)], J1)
            for m in range(dx):
                a[m][n] = col[m]
    if J2:
        for m in range(dx):
            a[m] = _taylor_shift(a[m], J2)
    return R(dict(((m, n), a[m][n]) for m in range(dx) for n in range(dy) if a[m][n]))


def specialization(Phi, J1, J2, P=None):
    r"""
    The coefficients (constant term first) of `\Phi(X + J_1, J_2) \in A[X]`,
    reduced modulo `P` if a prime `P` is given.
    """
    A = Phi.parent().base_ring()
    J1, J2 = A(J1), A(J2)
    red = (lambda c: c % P) if P is not None else (lambda c: c)
    J1, J2 = red(J1), red(J2)
    d = coefficient_dict(Phi)
    dx = max(m for m, _ in d) + 1
    dy = max(n for _, n in d) + 1
    powers = [A.one()]
    for _ in range(dy - 1):
        powers.append(red(powers[-1] * J2))
    f = [A.zero()] * dx
    for (m, n), c in d.items():
        f[m] = f[m] + red(c) * powers[n]
    f = [red(c) for c in f]
    if J1:
        f = [red(c) for c in _taylor_shift_mod(f, J1, red)]
    return f


def _taylor_shift_mod(c, J, red):
    c = list(c)
    n = len(c)
    for i in range(n - 1):
        for k in range(n - 2, i - 1, -1):
            c[k] = red(c[k] + J * c[k + 1])
    return c


def C_J(Phi, J1=0, J2=None, P=None):
    r"""
    Return `C_{J_1,J_2}(N,P) = \mathrm{ord}_X(\Phi_N(X+J_1, J_2) \bmod P)`, or
    `C_{J_1,J_2}(N,0) = \mathrm{ord}_X\,\Phi_N(X+J_1,J_2)` if ``P`` is ``None``.
    By default `J_2 = J_1`, giving the numbers `C_J(N,P)` of the paper.

    EXAMPLES:

    For `\deg P = 1` one has `C_0(N,P) = \psi(N)` (Proposition 2.3)::

        sage: from drinfeld_modpoly import drinfeld_modular_polynomial
        sage: from drinfeld_modpoly.analysis import C_J
        sage: A.<T> = GF(2)[]
        sage: Phi = drinfeld_modular_polynomial(T^2 + T + 1)
        sage: C_J(Phi), C_J(Phi, P=T), C_J(Phi, P=T^3 + T + 1)
        (2, 5, 2)
    """
    if J2 is None:
        J2 = J1
    f = specialization(Phi, J1, J2, P)
    c = 0
    for coeff in f:
        if coeff != 0:
            break
        c += 1
    return ZZ(c)


def n_opt(Phi, P, C):
    r"""
    Return ``(n, where)``: the minimum `n_{\mathrm{opt}}` of
    `v_P(a_{m,n})/(C - m - n)` over the nonzero coefficients of ``Phi`` with
    `m + n < C`, and the list of pairs `(m,n)` at which it is attained.
    If there is no such coefficient, return ``(None, [])``.
    """
    best, where = None, []
    for (m, n), a in sorted(coefficient_dict(Phi).items()):
        if m + n >= C:
            continue
        r = QQ(valuation(a, P)) / (C - m - n)
        if best is None or r < best:
            best, where = r, [(m, n)]
        elif r == best:
            where.append((m, n))
    return best, where


def bound_holds(Phi, P, C, const):
    r"""
    Whether `v_P(a_{m,n}) \ge \mathrm{const}\cdot(C - m - n)` for all
    coefficients of ``Phi`` with `m + n < C`.
    """
    return all(valuation(a, P) >= const * (C - m - n)
               for (m, n), a in coefficient_dict(Phi).items() if m + n < C)


def vanishes_below(Phi, C):
    r"""Whether `a_{m,n} = 0` for all `m + n < C`."""
    return all(m + n >= C for (m, n) in coefficient_dict(Phi))


def kronecker_congruence(Phi, N):
    r"""
    Whether `\Phi \equiv (X^{|N|} - Y)(X - Y^{|N|}) \pmod N`; this holds for
    `\Phi = \Phi_N` with `N` prime [Bae 1992, Thm. 3.1].
    """
    R = Phi.parent()
    X, Y = R.gens()
    n = ZZ(N.base_ring().cardinality()) ** N.degree()
    rhs = coefficient_dict((X ** n - Y) * (X - Y ** n))
    lhs = dict((k, c % N) for k, c in coefficient_dict(Phi).items() if c % N != 0)
    return lhs == rhs


def newton_root_valuations(f, P):
    r"""
    The multiset of `P`-adic valuations of the roots of a polynomial over
    `A`, read off its Newton polygon.

    INPUT: ``f`` -- a polynomial over `A`, or the list of its coefficients
    (constant term first).

    OUTPUT: a dictionary ``{valuation: multiplicity}``; the root `0` is
    recorded with valuation ``+Infinity``.

    EXAMPLES::

        sage: from drinfeld_modpoly import drinfeld_modular_polynomial_at_zero
        sage: from drinfeld_modpoly.analysis import newton_root_valuations
        sage: A.<T> = GF(2)[]
        sage: f = drinfeld_modular_polynomial_at_zero(T^3 + T + 1)
        sage: newton_root_valuations(f, T + 1) == {3: 6, 6: 3}
        True
    """
    coeffs = f if isinstance(f, (list, tuple)) else f.list()
    pts = [(i, valuation(c, P)) for i, c in enumerate(coeffs) if c != 0]
    z = pts[0][0]
    hull = [pts[0]]
    for pt in pts[1:]:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    out = {Infinity: ZZ(z)} if z else {}
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        slope = QQ(y1 - y2) / (x2 - x1)
        out[slope] = out.get(slope, 0) + ZZ(x2 - x1)
    return out


def apply_automorphism(Phi, a, b=0):
    r"""
    Transport `\Phi = \Phi_N` along the automorphism `\sigma : T \mapsto aT + b`
    of `A` (`a \in \GF{q}^*`, `b \in \GF{q}`): return `\Phi_{\sigma(N)}`, where
    `\sigma(N) = N(aT+b)` made monic.

    If `\varphi_T = T + g\tau + \Delta\tau^2`, the conjugate module
    `\varphi^\sigma` has `\varphi^\sigma_T = T + a^{-1}\sigma(g)\tau + a^{-1}\sigma(\Delta)\tau^2`
    and hence `j(\varphi^\sigma) = \sigma(j(\varphi))/a`; consequently

    .. MATH::

        \Phi_{\sigma(N)}(X, Y) = a^{-\psi(N)}\,\sigma(\Phi_N)(aX, aY),

    where `\sigma` acts on the coefficients.  For a translation
    `T \mapsto T + b` this is simply `\Phi_{\sigma(N)} = \sigma(\Phi_N)`, as
    used in Section 4 of the paper.

    EXAMPLES::

        sage: from drinfeld_modpoly import drinfeld_modular_polynomial
        sage: from drinfeld_modpoly.analysis import apply_automorphism
        sage: A.<T> = GF(3)[]
        sage: Phi = drinfeld_modular_polynomial(T + 1)
        sage: apply_automorphism(Phi, 1, 1) == drinfeld_modular_polynomial(T + 2)
        True
        sage: apply_automorphism(Phi, 2, 0) == drinfeld_modular_polynomial(T + 2)
        True
    """
    R = Phi.parent()
    A = R.base_ring()
    Fq = A.base_ring()
    a, b = Fq(a), Fq(b)
    image = a * A.gen() + b
    d = coefficient_dict(Phi)
    top = max(m for m, _ in d)
    return R(dict(((m, n), a ** (m + n - top) * c(image)) for (m, n), c in d.items()))
