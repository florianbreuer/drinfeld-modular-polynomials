# -*- coding: utf-8 -*-
r"""
Closed forms: two families of singular moduli, and the Bassa--Beelen formula
for `\Phi_T`.
"""
from sage.all import ZZ, PolynomialRing, binomial


def sqrtT_singular_modulus(A):
    r"""
    The singular modulus `J_s = T^{(q+1)/2}\,(1 + T^{(q-1)/2})^{q+1}` (`q` odd):
    the `j`-invariant of the Drinfeld module `\rho_T = (\sqrt T + \tau)^2`
    with complex multiplication by `\GF{q}[\sqrt T]` (Section 4.1 of the paper).

    EXAMPLES::

        sage: from drinfeld_modpoly.special import sqrtT_singular_modulus
        sage: A.<T> = GF(3)[]
        sage: sqrtT_singular_modulus(A).factor()
        T^2 * (T + 1)^4
    """
    q = ZZ(A.base_ring().cardinality())
    if q % 2 == 0:
        raise ValueError("J_s is defined for odd q only")
    T = A.gen()
    return T ** ((q + 1) // 2) * (1 + T ** ((q - 1) // 2)) ** (q + 1)


def conductor_singular_modulus(A):
    r"""
    The singular modulus `J_c = (-1)^q\,T\,(T^{q-1} - 1)^{q+1}`: the
    `j`-invariant with complex multiplication by the order
    `A + T\,\GF{q^2}[T]` of conductor `T` in `\GF{q^2}[T]`
    (Proposition 4.5 of the paper).

    EXAMPLES::

        sage: from drinfeld_modpoly.special import conductor_singular_modulus
        sage: A.<T> = GF(2)[]
        sage: conductor_singular_modulus(A).factor()
        T * (T + 1)^3
    """
    q = ZZ(A.base_ring().cardinality())
    T = A.gen()
    return (-1) ** q * T * (T ** (q - 1) - 1) ** (q + 1)


def bassa_beelen_phi_T(A, names=('X', 'Y')):
    r"""
    The closed form of Bassa and Beelen for `\Phi_T(X,Y)` over
    `A = \GF{q}[T]` (conjectured by Schweizer):

    .. MATH::

        \Phi_T = (X+Y-j_0)^{q+1} - XY^q - X^qY + (XY)^q(T^{1-q}-1)
        + XY(T^{q-1}-1)^{q^2}
        - T^{1-q}XY\sum_{i=0}^{\lfloor (q-1)/2\rfloor} C_i\,
        \bigl(XY - T^q(X+Y-j_0)\bigr)^{q-1-2i}\bigl(XY\,T^{q^2+1}\bigr)^i,

    where `j_0 = -T(T^{q-1}-1)^{q+1}` and `C_i = \binom{2i}{i} - \binom{2i}{i-1}`
    is the `i`-th Catalan number.

    REFERENCE: A. Bassa, P. Beelen, *A closed form expression for the Drinfeld
    modular polynomial* `\Phi_T(X,Y)`, Arch. Math. (Basel) 99 (2012), 237--245,
    Theorem 9 and equation (12).

    This is completely independent of the deformation algorithm, and is used
    as an external check.
    """
    q = ZZ(A.base_ring().cardinality())
    T = A.gen()
    R = PolynomialRing(A, list(names))
    X, Y = R.gens()
    j0 = -T * (T ** (q - 1) - 1) ** (q + 1)
    L = X + Y - j0
    # G = T^(q-1) * Phi_T is a polynomial in T
    G = T ** (q - 1) * L ** (q + 1) - T ** (q - 1) * (X * Y ** q + X ** q * Y) \
        + (X * Y) ** q * (1 - T ** (q - 1)) \
        + T ** (q - 1) * (T ** (q - 1) - 1) ** (q ** 2) * X * Y
    base = X * Y - T ** q * L
    S = R.zero()
    for i in range((q - 1) // 2 + 1):
        catalan = binomial(2 * i, i) - (binomial(2 * i, i - 1) if i else 0)
        S += catalan * base ** (q - 1 - 2 * i) * (X * Y * T ** (q ** 2 + 1)) ** i
    G -= X * Y * S
    coeffs = {}
    for k, c in G.dict().items():
        quo, rem = c.quo_rem(T ** (q - 1))
        if rem != 0:
            raise ArithmeticError("T^(q-1) does not divide a coefficient")
        coeffs[k] = quo
    return R(coeffs)
