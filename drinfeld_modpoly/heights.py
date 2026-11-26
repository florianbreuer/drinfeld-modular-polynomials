# -*- coding: utf-8 -*-
r"""
Degrees and heights of Drinfeld modular polynomials.

Throughout, `A = \GF{q}[T]` and `N \in A` is monic of positive degree.  The
Drinfeld modular polynomial `\Phi_N(X,Y) \in A[X,Y]` has degree

.. MATH::

    \psi(N) = |N| \prod_{P \mid N} (1 + |P|^{-1}), \qquad |N| = q^{\deg N},

in each variable, and its height `h(\Phi_N)` (the largest `T`-degree of a
coefficient) satisfies, by Breuer--Pazuki--Ran [BPR2024, Thm. 1.1],

.. MATH::

    h(\Phi_N) = \frac{q^2-1}{2}\,\psi(N)\,\bigl(\deg N - 2\lambda_N + b_q(N)\bigr),
    \qquad 0 \le b_q(N) \le B_q := 4 + \frac{5q^3-q^2-q+1}{q(q+1)(q-1)^2},

where `\lambda_N = \sum_{P^n \| N} \frac{|P|^n-1}{|P|^{n-1}(|P|^2-1)} \deg P`.
The upper bound is what makes the output of
:func:`drinfeld_modpoly.modular_polynomial.drinfeld_modular_polynomial`
provably exact.

The constant `B_q` is the one of the third arXiv version (v3, November 2026)
of [BPR2024]; it equals `4 + 1/q + 4q^2/((q-1)^2(q+1))`, e.g. `59/6` for
`q = 2`.  (Versions 1 and 2 stated larger constants, so bounds computed
with them remain valid.)

REFERENCES:

- [BPR2024] F. Breuer, F. Pazuki, Z. Ran, *Heights of Drinfeld modular
  polynomials and Hecke images*, arXiv:2410.11132v3.
"""
from sage.all import QQ, ZZ, floor


def _check_level(N):
    r"""
    Validate a level and return ``(A, Fq, q)``.
    """
    A = N.parent()
    Fq = A.base_ring()
    if not (Fq.is_field() and Fq.is_finite()):
        raise TypeError("the level N must be a polynomial over a finite field")
    if N.degree() < 1 or not N.is_monic():
        raise ValueError("the level N must be monic of positive degree")
    return A, Fq, ZZ(Fq.cardinality())


def psi(N):
    r"""
    Return `\psi(N) = |N| \prod_{P \mid N}(1 + |P|^{-1})`, the degree of
    `\Phi_N(X,Y)` in each variable (the number of cyclic submodules of
    `(A/N)^2` isomorphic to `A/N`).

    EXAMPLES::

        sage: from drinfeld_modpoly import psi
        sage: A.<T> = GF(3)[]
        sage: psi(T), psi(T^2 + 1), psi(T*(T + 1)), psi((T + 1)^2)
        (4, 10, 16, 12)
    """
    _, _, q = _check_level(N)
    out = ZZ(1)
    for P, n in N.factor():
        nP = q ** P.degree()
        out *= nP ** n + nP ** (n - 1)
    return out


def lambda_N(N):
    r"""
    Return `\lambda_N = \sum_{P^n \| N} \frac{|P|^n-1}{|P|^{n-1}(|P|^2-1)} \deg P`
    (a rational number).
    """
    _, _, q = _check_level(N)
    out = QQ(0)
    for P, n in N.factor():
        nP = q ** P.degree()
        out += QQ(nP ** n - 1) / (nP ** (n - 1) * (nP ** 2 - 1)) * P.degree()
    return out


def B_q(q):
    r"""
    Return the constant `B_q = 4 + \frac{5q^3-q^2-q+1}{q(q+1)(q-1)^2}` of
    [BPR2024, Thm. 1.1].

    EXAMPLES::

        sage: from drinfeld_modpoly import B_q
        sage: B_q(2), B_q(3), B_q(4)
        (59/6, 79/12, 1021/180)
    """
    q = ZZ(q)
    return 4 + QQ(5 * q ** 3 - q ** 2 - q + 1) / (q * (q + 1) * (q - 1) ** 2)


def height_bound(N):
    r"""
    Return the proven upper bound

    .. MATH::

        h := \Bigl\lfloor \frac{q^2-1}{2}\,\psi(N)\,\bigl(\deg N - 2\lambda_N + B_q\bigr) \Bigr\rfloor
        \;\ge\; h(\Phi_N)

    for the height of `\Phi_N` [BPR2024, Thm. 1.1].

    EXAMPLES:

    At level `T` over `\GF{2}` the bound is 45, while the true height is
    `q^2(q+1) = 12`::

        sage: from drinfeld_modpoly import height_bound
        sage: A.<T> = GF(2)[]
        sage: height_bound(T)
        45
    """
    _, _, q = _check_level(N)
    return ZZ(floor(QQ(q * q - 1) / 2 * psi(N) * (N.degree() - 2 * lambda_N(N) + B_q(q))))


def height(Phi):
    r"""
    Return the height of a polynomial with coefficients in `A = \GF{q}[T]`:
    the largest `T`-degree of a coefficient.
    """
    return max(c.degree() for c in Phi.coefficients())


def b_q(N, h):
    r"""
    Return the quantity `b_q(N)` defined by
    `h = \frac{q^2-1}{2}\psi(N)(\deg N - 2\lambda_N + b_q(N))`, for a given
    height ``h``.  By [BPR2024, Thm. 1.1], `0 \le b_q(N) \le B_q` when
    `h = h(\Phi_N)`.
    """
    _, _, q = _check_level(N)
    return QQ(2 * h) / ((q * q - 1) * psi(N)) - N.degree() + 2 * lambda_N(N)
