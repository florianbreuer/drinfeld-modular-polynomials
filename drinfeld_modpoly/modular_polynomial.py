# -*- coding: utf-8 -*-
r"""
Drinfeld modular polynomials by deformation at a place of `A = \GF{q}[T]`.

For a monic `N \in A` of positive degree, the Drinfeld modular polynomial
`\Phi_N(X,Y) \in A[X,Y]` vanishes exactly at the pairs of `j`-invariants of
rank 2 Drinfeld `A`-modules linked by a cyclic isogeny of degree `N`.  This
module computes it *exactly*, for an arbitrary level `N` and an arbitrary
prime power `q`, by Algorithm 1 of

    F. Breuer, F. Pazuki, *Divisibility of the coefficients of Drinfeld
    modular polynomials*.

ALGORITHM:

Fix a monic prime `P \nmid N` of degree `d_P`.  All computations take place in
the finite ring `R = E[\pi]/(\pi^K)`, where `E` is a finite field containing
`\GF{P} = A/P` and the `N`-torsion of the reduction of
`\phi^0 : T \mapsto T + \tau^2` (the module with `j = 0`), and `\pi`
stands for `P`.  The ring `R` is an `A`-algebra via `T \mapsto t`, the root of
`P(t) = \pi` with `t \equiv \theta_P \bmod \pi`.

1. For `\psi(N)+1` values `\varepsilon_s \in E^*` with pairwise distinct
   `(q+1)`-st powers, consider the deformation
   `\tilde\varphi^s : T \mapsto t + \varepsilon_s\pi\,\tau + \tau^2` of `\phi^0`;
   its `j`-invariant is `y_s = (\varepsilon_s\pi)^{q+1}`.
2. Lift the `N`-torsion of the reduction to `R` by Newton iteration, form the
   kernel polynomial `u_C` of each of the `\psi(N)` cyclic kernels `C`, and
   read off `j(\tilde\varphi^s/C)` from the top coefficients of
   `u_C\tilde\varphi^s_T = (\tilde\varphi^s/C)_T u_C`.
3. Then `\Phi_N(X, y_s) = \prod_C (X - j(\tilde\varphi^s/C))`; interpolate in
   `Y` through the `\psi(N)+1` nodes `y_s`.  This costs exactly
   `(q+1)\psi(N)` digits of `\pi`-adic precision.
4. Recover each coefficient `a_{m,n} \in A` from its `P`-adic expansion
   `a_{m,n} = \sum_k r_k P^k`, `\deg r_k < d_P`.

With the proven height bound `h \ge h(\Phi_N)` of Breuer--Pazuki--Ran
(:func:`drinfeld_modpoly.heights.height_bound`) and precision
`K > h/d_P + (q+1)\psi(N)`, the output is provably the exact `\Phi_N`
(Proposition 5.1 of the paper).  We run with 12 digits to spare and check
that all the spare digits vanish.

Two remarks on the implementation, both immediate from the paper:

- the lifted torsion `\tilde\varphi^s[N] \subset R` is an `\GF{q}`-vector
  space reducing isomorphically onto the torsion in `E`, so it suffices to
  lift an `\GF{q}`-basis (`2\deg N` Newton iterations instead of `q^{2\deg N}`);
- the interpolation nodes are `y_s = c_s\pi^{q+1}` with `c_s = \varepsilon_s^{q+1} \in E`,
  so Lagrange interpolation amounts to inverting a Vandermonde matrix *over
  the field* `E`, followed by an exact division by `\pi^{(q+1)n}`.
"""
from __future__ import print_function

import sys
import time

from sage.all import ZZ, GF, PolynomialRing, matrix, vector

from drinfeld_modpoly.heights import _check_level, psi as _psi, height_bound as _height_bound
from drinfeld_modpoly.reduction import (ReducedDrinfeldModule, FieldEmbedding, _coords,
                                        _extension_field, skew_evaluate, _frobenius_order)
from drinfeld_modpoly.util import monic_polynomials


# ------------------------------------------------------------ choice of place

def torsion_field_degree(N, P):
    r"""
    The degree `m` over `\GF{q}` of the smallest field containing `\GF{P}`
    and the `N`-torsion of the reduction of `\phi^0 : T \mapsto T + \tau^2`
    at the monic prime `P \nmid N`.
    """
    A, Fq, q = _check_level(N)
    dP = P.degree()
    FP = _extension_field(ZZ(Fq.characteristic()), ZZ(Fq.degree()) * dP, 'b')
    emb = FieldEmbedding(Fq, FP)
    theta = PolynomialRing(FP, 'x')(emb.poly(P)).roots(multiplicities=False)[0]
    phiN = skew_evaluate(emb.poly(N), [theta, FP.zero(), FP.one()], q)
    return dP * _frobenius_order(phiN, q, dP)


def choose_place(N):
    r"""
    The default base place for the level `N`: among the monic primes
    `P \nmid N` of smallest degree, one for which the working field `E` is
    smallest.

    EXAMPLES:

    For `q = 2` the level `T(T+1)` is divisible by both primes of degree one,
    so the base place has degree two::

        sage: from drinfeld_modpoly import choose_place
        sage: A.<T> = GF(2)[]
        sage: choose_place(T*(T + 1))
        T^2 + T + 1
        sage: choose_place(T^3 + T + 1)
        T
    """
    A, Fq, q = _check_level(N)
    d = 1
    while True:
        cands = [P for P in monic_polynomials(A, d)
                 if P.is_irreducible() and not P.divides(N)]
        if cands:
            return min(cands, key=lambda P: torsion_field_degree(N, P))
        d += 1


# ------------------------------------------------------- the ring E[pi]/(pi^K)

class TruncatedSeriesRing(object):
    r"""
    The ring `R = E[\pi]/(\pi^K)`; its elements are represented by
    polynomials in `\pi` of degree `< K` over the finite field `E`.
    """
    def __init__(self, E, K, q):
        self.E, self.K, self.q = E, ZZ(K), ZZ(q)
        self.S = PolynomialRing(E, 'pi')
        self.pi = self.S.gen()
        self.zero, self.one = self.S.zero(), self.S.one()

    def mul(self, f, g):
        return (f * g).truncate(self.K)

    def scale(self, c, f):
        r"""``c * f`` for a constant ``c`` in `E`."""
        if not c:
            return self.zero
        if c.is_one():
            return f
        return c * f

    def shift(self, f, n):
        r"""``pi^n * f``."""
        return f.shift(n).truncate(self.K)

    def frobenius(self, f, n=1):
        r"""
        `f \mapsto f^{q^n}`.  Only the first `\lceil K/q^n\rceil` coefficients
        of `f` contribute.
        """
        Q = self.q ** n
        f = f.truncate(-(-self.K // Q))
        if f.degree() <= 0:
            return self.S(f[0] ** Q)
        if Q <= 5:
            return f ** Q
        return self.S(dict((Q * k, c ** Q) for k, c in enumerate(f.list()) if c))

    def power(self, f, n):
        r"""`f^n` for `n \ge 1`, by binary powering."""
        result, base = None, f
        while True:
            if n & 1:
                result = base if result is None else self.mul(result, base)
            n >>= 1
            if not n:
                return result
            base = self.mul(base, base)

    def inverse(self, f):
        r"""The inverse of a unit, by Newton iteration."""
        y, prec = self.S(~f[0]), 1
        while prec < self.K:
            prec = min(2 * prec, self.K)
            y = (y * (2 - (f.truncate(prec) * y).truncate(prec))).truncate(prec)
        return y

    def evaluate(self, coeffs, x):
        r"""`\sum_i c_i x^i` for constants `c_i \in E` and `x \in R`."""
        out = self.zero
        for c in reversed(coeffs):
            out = self.mul(out, x) + c
        return out


# ------------------------------------------------------------ the local stage

class _Deformer(object):
    r"""
    Lifts the `N`-torsion of `\bar\phi^0` to the deformations
    `T \mapsto t + \varepsilon\pi\tau + \tau^2` over `R = E[\pi]/(\pi^K)` and
    computes the `j`-invariants of their cyclic `N`-isogenous quotients.
    """
    def __init__(self, M, K):
        self.M = M
        self.R = R = TruncatedSeriesRing(M.E, K, M.q)
        self.q, self.d, self.dP = M.q, M.d, M.dP
        # gamma(T) = t: the root of P(t) = pi with t = theta_P mod pi
        if self.dP == 1:
            self.t = R.S(M.theta) + R.pi
        else:
            Pc = M.emb.poly(M.P)
            dPc = [i * c for i, c in enumerate(Pc)][1:]
            t = R.S(M.theta)
            for _ in range(2 * ZZ(K).nbits() + 2):
                r = R.evaluate(Pc, t) - R.pi
                if r.is_zero():
                    break
                t = t - R.mul(r, R.inverse(R.evaluate(dPc, t)))
            else:
                raise ArithmeticError("Hensel lifting of t failed")
            self.t = t
        self.Nc = M.emb.poly(M.N)
        self.Ninv = R.inverse(R.evaluate(self.Nc, self.t))      # N(t)^(-1)

    def mul_t(self, v):
        R = self.R
        if self.dP == 1:
            return R.scale(self.M.theta, v) + R.shift(v, 1)
        return R.mul(self.t, v)

    def phi_T(self, v, eps):
        r"""`\tilde\varphi_T(v) = t v + \varepsilon\pi v^q + v^{q^2}`."""
        R = self.R
        vq = R.frobenius(v)
        out = self.mul_t(v) + R.frobenius(vq)
        if eps:
            out = out + R.scale(eps, R.shift(vq, 1))
        return out

    def phi_N(self, v, eps):
        R = self.R
        out, cur = R.zero, v
        for i, c in enumerate(self.Nc):
            if c:
                out = out + R.scale(c, cur)
            if i + 1 < len(self.Nc):
                cur = self.phi_T(cur, eps)
        return out

    def lift(self, w, eps):
        r"""
        The unique root of `\tilde\varphi_N` in `R` reducing to the torsion
        point `w \in E`: Newton iteration `x \leftarrow x - N(t)^{-1}\tilde\varphi_N(x)`
        (the derivative of the `\GF{q}`-linear polynomial `\tilde\varphi_N` is
        its lowest coefficient `N(t)`, a unit).
        """
        R = self.R
        x = R.S(w)
        for _ in range(ZZ(R.K).nbits() + 2):
            r = self.phi_N(x, eps)
            if r.is_zero():
                return x
            x = x - R.mul(self.Ninv, r)
        raise ArithmeticError("Newton lifting of a torsion point failed")

    def kernel_polynomial(self, flag):
        r"""
        Coefficients `[u_0, \dots, u_d]` of `u_C = \prod_{c\in C}(x - c)` for
        the `\GF{q}`-span `C` of ``flag``, by the subspace recursion
        `e_{V+\GF{q}v} = e_V^q - e_V(v)^{q-1}e_V`.
        """
        R = self.R
        u = [R.one]
        for w in flag:
            c, x = R.zero, w
            for i, a in enumerate(u):                     # c = e_V(w)
                c = c + (x if a.is_one() else R.mul(a, x))
                if i + 1 < len(u):
                    x = R.frobenius(x)
            c = R.power(c, self.q - 1)
            new = []
            for i in range(len(u) + 1):
                term = R.frobenius(u[i - 1]) if i >= 1 else R.zero
                if i < len(u):
                    term = term - (c if u[i].is_one() else R.mul(c, u[i]))
                new.append(term)
            u = new
        return u

    def isogenous_j(self, eps):
        r"""
        The list of `j(\tilde\varphi/C) \in R` over the cyclic kernels `C` of
        `\tilde\varphi : T \mapsto t + \varepsilon\pi\tau + \tau^2`.
        """
        R, M, q, d = self.R, self.M, self.q, self.d
        lifted = [self.lift(b, eps) for b in M.basis]
        Q = q ** d                                         # g^(q^d), g = eps*pi
        g_top = R.S({Q: eps ** Q}) if (eps and Q < R.K) else R.zero
        js = []
        for C in M.kernels:
            w = R.zero
            for c, b in zip(C.coordinates, lifted):
                if c:
                    w = w + R.scale(c, b)
            flag = [w]
            for _ in range(d - 1):
                flag.append(self.phi_T(flag[-1], eps))
            u = self.kernel_polynomial(flag)
            # g' = g^(q^d) + u_(d-1) - u_(d-1)^(q^2),  j' = g'^(q+1)   (Delta = Delta' = 1)
            gp = g_top + u[d - 1] - R.frobenius(u[d - 1], 2)
            js.append(R.mul(R.frobenius(gp), gp))
        return js

    def product(self, js):
        r"""Coefficients (constant term first) of `\prod_j (X - j)`."""
        R = self.R
        coeffs = [R.one]
        for j in js:
            new = [R.zero] + coeffs
            for i, c in enumerate(coeffs):
                new[i] = new[i] - (j if c.is_one() else R.mul(j, c))
            coeffs = new
        return coeffs


class _Recognizer(object):
    r"""
    Recovers `a \in A` from the first `J` digits of `\gamma(a) \in E[[\pi]]`:
    writing `a = \sum_k r_kP^k` with `\deg r_k < d_P`, one has
    `\gamma(a) = \sum_k r_k(t)\pi^k` and `r_k(t) \equiv r_k(\theta_P) \bmod \pi`.

    Three conditions are enforced: every residue lies in the subfield `\GF{P}`
    of `E`; the digits `r_k` with `k > h/d_P` vanish; and `\deg a \le h`.
    """
    def __init__(self, deformer, J, h):
        M = self.M = deformer.M
        self.R, self.t = deformer.R, deformer.t
        self.J, self.h = ZZ(J), ZZ(h)
        self.A, self.P, self.dP = M.A, M.P, M.dP
        E, Fq, p, e = M.E, M.Fq, M.p, M.e
        # an F_p-basis y^a theta^b of F_P inside E, and a left inverse
        ypow = [M.emb(Fq.gen() ** a) for a in range(e)] if e > 1 else [E.one()]
        rows, tb = [], E.one()
        for _ in range(self.dP):
            rows += [_coords(ya * tb, E) for ya in ypow]
            tb = tb * M.theta
        self._B = matrix(GF(p), rows)
        self._piv = list(self._B.pivots())
        assert len(self._piv) == e * self.dP
        self._Binv = self._B.matrix_from_columns(self._piv).inverse()
        self._digit = {}
        self._digit_series = {}
        self._Ppow = {}

    def decode(self, x):
        r"""The `r \in A`, `\deg r < d_P`, with `r(\theta_P) = x \in \GF{P} \subseteq E`."""
        try:
            return self._digit[x]
        except KeyError:
            pass
        M = self.M
        v = vector(GF(M.p), _coords(x, M.E))
        sol = vector(GF(M.p), [v[i] for i in self._piv]) * self._Binv
        if sol * self._B != v:
            raise ArithmeticError("a residue does not lie in the residue field F_P")
        e, Fq = M.e, M.Fq
        if e == 1:
            cs = [Fq(sol[b]) for b in range(self.dP)]
        else:
            y = Fq.gen()
            cs = [sum((Fq(sol[b * e + a]) * y ** a for a in range(e)), Fq.zero())
                  for b in range(self.dP)]
        r = self._digit[x] = self.A(cs)
        return r

    def _series(self, r):
        r"""`r(t) \in R` for a digit `r`."""
        try:
            return self._digit_series[r]
        except KeyError:
            s = self._digit_series[r] = self.R.evaluate(self.M.emb.poly(r), self.t)
            return s

    def _from_digits(self, digits):
        r"""`\sum_k r_k P^k`, by divide and conquer."""
        n = len(digits)
        if n == 0:
            return self.A.zero()
        if n == 1:
            return digits[0]
        half = n // 2
        if half not in self._Ppow:
            self._Ppow[half] = self.P ** half
        return self._from_digits(digits[:half]) \
            + self._Ppow[half] * self._from_digits(digits[half:])

    def __call__(self, x):
        x = x.truncate(self.J)
        if self.dP == 1:
            # t = theta + pi: the digits are the coefficients, constants in F_q
            digits = [self.decode(c) for c in x.list()]
        else:
            digits = []
            while not x.is_zero():
                r = self.decode(x[0])
                digits.append(r)
                if r:
                    x = x - self._series(r).truncate(self.J - len(digits) + 1)
                x = x.shift(-1)
        if len(digits) > self.h // self.dP + 1:
            raise ArithmeticError("a digit beyond the height bound is nonzero")
        a = self._from_digits(digits)
        if a.degree() > self.h:
            raise ArithmeticError("a coefficient exceeds the height bound")
        return a


def _deformation_parameters(E, q, count):
    r"""
    The first ``count`` elements of `E^*`, in the order
    `x_n = \sum_i n_i z^i` (`n = \sum_i n_ip^i`), having pairwise distinct
    `(q+1)`-st powers.
    """
    p, z = ZZ(E.characteristic()), E.gen()
    zpow = [z ** i for i in range(E.degree())]
    out, seen = [], set()
    for n in range(1, E.cardinality()):
        x = sum((a * zi for a, zi in zip(ZZ(n).digits(p), zpow)), E.zero())
        y = x ** (q + 1)
        if y not in seen:
            seen.add(y)
            out.append(x)
            if len(out) == count:
                return out
    raise ArithmeticError("the field E is too small")


def _precision(N, P, h, loss, extra_digits):
    r"""
    The height bound in force and the working precision
    `K = \lceil h/d_P\rceil + \mathrm{loss} + \mathrm{extra}`.
    """
    hb = _height_bound(N) if h is None else ZZ(h)
    if extra_digits < 1:
        raise ValueError("extra_digits must be at least 1")
    return hb, -((-hb) // P.degree()) + loss + extra_digits


def _log(verbose, msg):
    if verbose:
        print(msg)
        sys.stdout.flush()


# ----------------------------------------------------------------- user level

def drinfeld_modular_polynomial(N, place=None, names=('X', 'Y'), h=None,
                                extra_digits=12, root_index=0,
                                certificate=False, verbose=False):
    r"""
    Return the Drinfeld modular polynomial `\Phi_N(X,Y) \in A[X,Y]`.

    INPUT:

    - ``N`` -- a monic polynomial of positive degree in `A = \GF{q}[T]`, for
      any prime power `q`
    - ``place`` -- (default: chosen by :func:`choose_place`) a monic prime `P`
      of `A` not dividing ``N``, at which the computation is carried out; the
      result does not depend on it
    - ``names`` -- names of the two variables of the result
    - ``h`` -- (default: the proven bound :func:`~drinfeld_modpoly.heights.height_bound`)
      an upper bound for the height of `\Phi_N`.  The output is proven to be
      correct only if ``h`` really is an upper bound.
    - ``extra_digits`` -- (default: 12) number of `P`-adic digits computed
      beyond `\lceil h/\deg P\rceil + (q+1)\psi(N)`; the superfluous digits are
      checked to vanish
    - ``root_index`` -- selects the root `\theta_P` of `P` (and the embedding
      of `\GF{q}`) used internally; the result does not depend on it
    - ``certificate`` -- if ``True``, also return a dictionary with the place,
      the precision `K`, the height bound, the degree of the working field `E`
      over `\GF{q}` and the running time
    - ``verbose`` -- print progress

    OUTPUT: `\Phi_N` as an element of `A[X,Y]` (and the certificate, if requested).

    EXAMPLES::

        sage: from drinfeld_modpoly import drinfeld_modular_polynomial
        sage: A.<T> = GF(2)[]
        sage: Phi = drinfeld_modular_polynomial(T)
        sage: X, Y = Phi.parent().gens()
        sage: Phi.degree(X), Phi.degree(Y), Phi(X, Y) == Phi(Y, X)
        (3, 3, True)
        sage: Phi(X, 0)
        X^3 + (T^4 + T^3 + T^2 + T)*X^2 + (T^8 + T^6 + T^4 + T^2)*X + T^12 + T^11 + T^4 + T^3
        sage: Phi(X, 0) == (X + T*(T + 1)^3)^3
        True

    The result is independent of the base place::

        sage: Phi == drinfeld_modular_polynomial(T, place=T^3 + T + 1)
        True

    With ``certificate=True`` one also gets the parameters of the computation::

        sage: Phi, cert = drinfeld_modular_polynomial(T, certificate=True)
        sage: cert["place"], cert["height_bound"], cert["precision"]
        (T + 1, 45, 66)

    Non-prime fields and composite levels are fine::

        sage: A.<T> = GF(4, 'y')[]
        sage: Phi4 = drinfeld_modular_polynomial(T)
        sage: Phi4.degree(Phi4.parent().gen(0))
        5
        sage: A.<T> = GF(2)[]
        sage: Phi = drinfeld_modular_polynomial(T^2 + T)
        sage: Phi.degree(Phi.parent().gen(0))
        9
    """
    t0 = time.time()
    A, Fq, q = _check_level(N)
    P = choose_place(N) if place is None else A(place)
    psi = _psi(N)
    loss = (q + 1) * psi
    hb, K = _precision(N, P, h, loss, extra_digits)
    M = ReducedDrinfeldModule(N, P, min_power_classes=psi + 1, root_index=root_index)
    _log(verbose, "Phi_N for q = %s, N = %s: psi(N) = %s, place P = %s, height bound %s, "
         "precision K = %s, E = GF(%s^%s)" % (q, N, psi, P, hb, K, q, M.m))
    D = _Deformer(M, K)
    R = D.R

    # Phi_N(X, y_s) = prod_C (X - j(phi^s/C)) for the deformations phi^s
    eps = _deformation_parameters(M.E, q, psi + 1)
    rows = []
    for s, ep in enumerate(eps):
        rows.append(D.product(D.isogenous_j(ep)))
        _log(verbose, "  deformation %d/%d done (%.1fs)" % (s + 1, psi + 1, time.time() - t0))

    # interpolation in Y: y_s = c_s pi^(q+1) with c_s = eps_s^(q+1) in E, so
    # (a_(m,n) pi^((q+1) n))_n = V^(-1) (Phi_N(X, y_s)_m)_s, V = (c_s^n)
    nodes = [ep ** (q + 1) for ep in eps]
    Vinv = matrix(M.E, [[c ** n for n in range(psi + 1)] for c in nodes]).inverse()
    recognize = _Recognizer(D, K - loss, hb)
    coeffs = {}
    for m in range(psi + 1):
        for n in range(psi + 1):
            x = R.zero
            for s in range(psi + 1):
                x = x + R.scale(Vinv[n, s], rows[s][m])
            if x.valuation() < (q + 1) * n:
                raise ArithmeticError("interpolation: unexpected denominator")
            a = recognize(x.shift(-(q + 1) * n))
            if a:
                coeffs[(m, n)] = a
        _log(verbose, "  coefficients of X^%d recovered (%.1fs)" % (m, time.time() - t0))

    # consistency: Phi_N is symmetric, and monic of degree psi(N) in X
    for (m, n), a in coeffs.items():
        if coeffs.get((n, m)) != a:
            raise ArithmeticError("the computed polynomial is not symmetric")
    if coeffs.get((psi, 0)) != 1 or any((psi, n) in coeffs for n in range(1, psi + 1)):
        raise ArithmeticError("the computed polynomial is not monic")

    Phi = PolynomialRing(A, list(names))(coeffs)
    if certificate:
        return Phi, dict(q=q, N=N, psi=psi, place=P, precision=K, height_bound=hb,
                         extension_degree=M.m, seconds=time.time() - t0)
    return Phi


def drinfeld_modular_polynomial_at_zero(N, place=None, name='X', h=None,
                                        extra_digits=12, root_index=0,
                                        certificate=False, verbose=False):
    r"""
    Return the univariate specialization `\Phi_N(X, 0) \in A[X]`.

    By the product formula, `\Phi_N(X,0) = \prod_C (X - j(\phi^0/C))` over the
    cyclic kernels `C \subset \phi^0[N]` of the module
    `\phi^0 : T \mapsto T + \tau^2`.  This needs neither deformations nor
    interpolation, and is much cheaper than the full `\Phi_N`.

    INPUT: as for :func:`drinfeld_modular_polynomial`.

    EXAMPLES::

        sage: from drinfeld_modpoly import drinfeld_modular_polynomial_at_zero
        sage: A.<T> = GF(3)[]
        sage: f = drinfeld_modular_polynomial_at_zero(T); f.factor()
        (X + T^9 + 2*T^7 + 2*T^3 + T)^4
        sage: T^9 + 2*T^7 + 2*T^3 + T == T*(T^2 - 1)^4
        True

    Here `-T(T^2-1)^4` is the `j`-invariant with complex multiplication by
    the order of conductor `T` in `\GF{9}[T]` (Proposition 4.5 of the paper).
    """
    t0 = time.time()
    A, Fq, q = _check_level(N)
    P = choose_place(N) if place is None else A(place)
    psi = _psi(N)
    hb, K = _precision(N, P, h, 0, extra_digits)
    M = ReducedDrinfeldModule(N, P, root_index=root_index)
    _log(verbose, "Phi_N(X,0) for q = %s, N = %s: psi(N) = %s, place P = %s, height bound %s, "
         "precision K = %s, E = GF(%s^%s)" % (q, N, psi, P, hb, K, q, M.m))
    D = _Deformer(M, K)
    row = D.product(D.isogenous_j(M.E.zero()))
    recognize = _Recognizer(D, K, hb)
    f = PolynomialRing(A, name)([recognize(c) for c in row])
    if certificate:
        return f, dict(q=q, N=N, psi=psi, place=P, precision=K, height_bound=hb,
                       extension_degree=M.m, seconds=time.time() - t0)
    return f
