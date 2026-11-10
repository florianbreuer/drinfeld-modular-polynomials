# -*- coding: utf-8 -*-
r"""
Small helpers for `A = \GF{q}[T]`: deterministic enumeration of field
elements, monic polynomials and monic primes, and valuations.

The enumeration order is defined in terms of coordinates only, so that it does
not depend on the SageMath version or on the implementation of the field.
"""
from itertools import product as _product
from sage.all import ZZ, Infinity

from drinfeld_modpoly.reduction import _coords


def field_elements(Fq):
    r"""
    The elements of the finite field ``Fq`` in a fixed order: `0, 1, \dots`
    for a prime field, and in general ordered by the integer
    `\sum_i c_i p^i` attached to `c = \sum_i c_i y^i` (``y = Fq.gen()``).

    EXAMPLES::

        sage: from drinfeld_modpoly.util import field_elements
        sage: field_elements(GF(4, 'y'))
        [0, 1, y, y + 1]
    """
    p = ZZ(Fq.characteristic())
    return sorted(Fq, key=lambda c: sum(a * p ** i for i, a in enumerate(_coords(c, Fq))))


def monic_polynomials(A, d):
    r"""
    Iterate over the monic polynomials of degree ``d`` in `A = \GF{q}[T]`, in a
    fixed order (the constant term varies slowest).
    """
    elts = field_elements(A.base_ring())
    one = A.base_ring().one()
    for tail in _product(elts, repeat=d):
        yield A(list(tail) + [one])


def monic_primes(A, d):
    r"""
    The list of monic primes of degree ``d`` in `A`.

    EXAMPLES::

        sage: from drinfeld_modpoly import monic_primes
        sage: A.<T> = GF(2)[]
        sage: monic_primes(A, 3)
        [T^3 + T^2 + 1, T^3 + T + 1]
    """
    return [P for P in monic_polynomials(A, d) if P.is_irreducible()]


def valuation(a, P):
    r"""
    The `P`-adic valuation `v_P(a)` of `a \in A` (``+Infinity`` for `a = 0`).
    """
    if a == 0:
        return Infinity
    v = 0
    while True:
        a, r = a.quo_rem(P)
        if r != 0:
            return ZZ(v)
        v += 1
