# -*- coding: utf-8 -*-
r"""
Rank 2 Drinfeld modules over finite fields: torsion, cyclic kernels, isogenies.

Let `A = \GF{q}[T]`, let `P \in A` be a monic prime and `\GF{P} = A/P`, with
`\theta_P` the residue of `T`.  A rank 2 Drinfeld module in characteristic `P`
is given by

.. MATH::

    \bar\varphi_T = \theta_P + \bar g\,\tau + \bar\Delta\,\tau^2,
    \qquad \tau : x \mapsto x^q,

and for a monic `N \in A` with `P \nmid N` its `N`-torsion `\bar\varphi[N]` is
an `\GF{q}`-vector space of dimension `2 \deg N` inside a finite extension `E`
of `\GF{P}`.  The class :class:`ReducedDrinfeldModule` computes `E`, the
torsion, the `\psi(N)` cyclic kernels `\bar C \cong A/N`, their kernel
polynomials and the quotients `\bar\varphi/\bar C`.

This is the finite-field stage of the deformation algorithm
(:mod:`drinfeld_modpoly.modular_polynomial`), and it is also used on its own
to count, without any height bound, the numbers

.. MATH::

    C_{J_1,J_2}(N,P) = \#\{\bar C \subset \bar\varphi^2[N] \text{ cyclic} :
    j(\bar\varphi^2/\bar C) = \bar J_1\}

of the paper (Lemma 2.1(ii)).
"""
from sage.all import GF, PolynomialRing, ZZ, matrix

from drinfeld_modpoly.heights import _check_level, psi as _psi


# ---------------------------------------------------------------- finite fields

def _coords(x, F):
    r"""
    Coordinates of ``x`` in the `\GF{p}`-basis `1, y, y^2, \dots` of the
    finite field ``F`` (``y = F.gen()``), as a list of Python ints.
    """
    n = F.degree()
    if n == 1:
        return [int(x)]
    return [int(c) for c in x.polynomial().padded_list(n)]


def _extension_field(p, M, name):
    r"""
    A model of `\GF{p^M}` with an explicitly chosen modulus (this avoids
    Conway polynomial lookups, which are slow or unavailable in large degree).
    """
    if M == 1:
        return GF(p)
    R = PolynomialRing(GF(p), 'x')
    return GF(p ** M, name, modulus=R.irreducible_element(M))


class FieldEmbedding(object):
    r"""
    An embedding `F \to E` of finite fields of the same characteristic, for
    arbitrary models of `F` and `E`: the generator of `F` is sent to a root in
    `E` of its minimal polynomial.

    Nothing computed in this package depends on which root is chosen.
    """
    def __init__(self, F, E, root_index=0):
        self.F, self.E = F, E
        n = F.degree()
        if n == 1:
            self._powers = [E.one()]
        else:
            roots = sorted(F.modulus().roots(E, multiplicities=False), key=str)
            r = roots[root_index % len(roots)]
            self._powers = [r ** i for i in range(n)]
        self._cache = {}

    def __call__(self, c):
        try:
            return self._cache[c]
        except KeyError:
            pass
        out = self.E.zero()
        for a, r in zip(_coords(c, self.F), self._powers):
            if a:
                out += a * r
        self._cache[c] = out
        return out

    def poly(self, f):
        r"""
        Coefficients (constant term first) of ``f`` `\in F[T]`, mapped to `E`.
        """
        return [self(c) for c in f.list()]


def _horner(coeffs, x, zero):
    out = zero
    for c in reversed(coeffs):
        out = out * x + c
    return out


# ------------------------------------------------------------ skew polynomials
#
# Elements of F{tau} (tau a = a^q tau) are lists [c_0, c_1, ...] standing for
# sum c_i tau^i, i.e. for the additive polynomial sum c_i x^(q^i).

def skew_mul(a, b, q):
    r"""
    Product in `F\{\tau\}`: `(\sum a_i\tau^i)(\sum b_j\tau^j) = \sum a_i b_j^{q^i}\tau^{i+j}`.
    """
    out = [a[0].parent().zero()] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if not ai:
            continue
        Q = q ** i
        for j, bj in enumerate(b):
            if bj:
                out[i + j] = out[i + j] + ai * bj ** Q
    return out


def skew_evaluate(Ncoeffs, phiT, q):
    r"""
    The skew polynomial `\varphi_N = N(\varphi_T)` for `N = \sum n_i T^i` with
    coefficients ``Ncoeffs`` in (the image of) `\GF{q}`, by Horner's rule.

    The coefficients `n_i` are central in `F\{\tau\}`, but the constant term
    `\theta_P` of `\varphi_T` is not as soon as `\deg P \ge 3`; this is why
    `\varphi_N` must be evaluated as a polynomial in the single operator
    `\varphi_T`.
    """
    acc = [Ncoeffs[-1]]
    for c in reversed(Ncoeffs[:-1]):
        acc = skew_mul(acc, phiT, q)
        acc[0] = acc[0] + c
    return acc


def _frobenius_order(f, q, step):
    r"""
    The least `k \ge 1` with `\tau^{k\cdot\mathrm{step}} \equiv 1` modulo the
    left ideal `F\{\tau\} f`, for a separable `f \in F\{\tau\}`.

    Since `u \equiv r \pmod{F\{\tau\}f}` means `u(x) \equiv r(x) \pmod{f(x)}`
    as ordinary polynomials, this is the least `k` such that all roots of the
    additive polynomial `f(x)` lie in `\GF{q^{k\cdot\mathrm{step}}}`.
    """
    m = len(f) - 1
    lc_inv = ~f[-1]
    red = [-lc_inv * c for c in f[:-1]]          # tau^m = sum red[j] tau^j
    one = f[0].parent().one()
    zero = f[0].parent().zero()
    target = [one] + [zero] * (m - 1)
    R = list(target)                              # tau^0
    k = 0
    while True:
        for _ in range(step):                     # R <- remainder of tau * R
            top = R[-1] ** q
            R = [zero] + [c ** q for c in R[:-1]]
            if top:
                R = [r + top * s for r, s in zip(R, red)]
        k += 1
        if R == target:
            return k


# ------------------------------------------------------------------ the module

class CyclicKernel(object):
    r"""
    A cyclic kernel `\bar C = A\cdot w \cong A/N` of a
    :class:`ReducedDrinfeldModule`.

    - ``generator`` -- the point `w`;
    - ``coordinates`` -- the coordinates of `w` (elements of `\GF{q}`, embedded
      in `E`) in the fixed `\GF{q}`-basis of the `N`-torsion;
    - ``flag`` -- the `\GF{q}`-basis `w, T\cdot w, \dots, T^{\deg N-1}\cdot w` of `\bar C`.
    """
    def __init__(self, generator, coordinates, flag):
        self.generator = generator
        self.coordinates = coordinates
        self.flag = flag


class ReducedDrinfeldModule(object):
    r"""
    The reduction at a monic prime `P` of the rank 2 Drinfeld module
    `\varphi_T = T + g\tau + \Delta\tau^2` (with `g, \Delta \in A`,
    `P \nmid \Delta`), together with its `N`-torsion, for a monic level `N`
    with `P \nmid N`.

    INPUT:

    - ``N`` -- monic polynomial of positive degree over a finite field `\GF{q}`
    - ``P`` -- monic irreducible polynomial not dividing ``N``
    - ``g``, ``Delta`` -- elements of `A` (default: `0` and `1`, the module
      `\phi^0` with `j = 0` and complex multiplication by `\GF{q^2}[T]`)
    - ``min_power_classes`` -- if positive, the field `E` is enlarged until
      `(|E|-1)/(q+1)` is at least this number (the deformation algorithm needs
      `\psi(N)+1` elements of `E^*` with distinct `(q+1)`-st powers)
    - ``root_index`` -- which root of `P` (and of the modulus of `\GF{q}`) to
      use; no result depends on it

    EXAMPLES:

    The nine cyclic `(T^3+T+1)`-isogenies from `\phi^0` in characteristic
    `T+1` over `\GF{2}`; three of the kernels have `S_C = u_1/u_0 \equiv 0`::

        sage: from drinfeld_modpoly import ReducedDrinfeldModule
        sage: A.<T> = GF(2)[]
        sage: M = ReducedDrinfeldModule(T^3 + T + 1, T + 1)
        sage: len(M.kernels)
        9
        sage: sum(1 for C in M.kernels if M.S(C) == 0)
        3
    """
    def __init__(self, N, P, g=0, Delta=1, min_power_classes=0, root_index=0):
        A, Fq, q = _check_level(N)
        P = A(P)
        if not (P.is_monic() and P.is_irreducible()):
            raise ValueError("the place P must be a monic prime")
        if P.divides(N):
            raise ValueError("the place P must not divide the level N")
        g, Delta = A(g), A(Delta)
        if P.divides(Delta):
            raise ValueError("bad reduction: P divides Delta")
        self.A, self.Fq, self.q = A, Fq, q
        self.p, self.e = ZZ(Fq.characteristic()), ZZ(Fq.degree())
        self.N, self.P = N, P
        self.d, self.dP = ZZ(N.degree()), ZZ(P.degree())
        self.psi = _psi(N)
        p, e, d, dP = self.p, self.e, self.d, self.dP

        # 1. the smallest m with dP | m and phibar[N] contained in F_{q^m}:
        #    m/dP is the order of the Frobenius of F_P on the N-torsion
        FP = _extension_field(p, e * dP, 'b')
        emb0 = FieldEmbedding(Fq, FP)
        theta0 = self._root_of_P(FP, emb0, 0)
        phiT0 = [theta0, _horner(emb0.poly(g), theta0, FP.zero()),
                 _horner(emb0.poly(Delta), theta0, FP.zero())]
        phiN0 = skew_evaluate(emb0.poly(N), phiT0, q)
        m = dP * _frobenius_order(phiN0, q, dP)
        mult = 1
        while (q ** (m * mult) - 1) // (q + 1) < min_power_classes:
            mult += 1
        self.m = m * mult

        # 2. the field E = F_{q^m} with F_q and F_P = F_q(theta) inside it
        E = _extension_field(p, e * self.m, 'z')
        self.E = E
        self.emb = FieldEmbedding(Fq, E, root_index)
        self.theta = self._root_of_P(E, self.emb, root_index)
        self.g = self.reduce(g)
        self.Delta = self.reduce(Delta)
        self.phiT = [self.theta, self.g, self.Delta]
        self.phiN = skew_evaluate(self.emb.poly(N), self.phiT, q)
        self._scalars = [self.emb(c) for c in Fq]

        # 3. the torsion: roots in E of the additive polynomial phibar_N(x)
        self.basis = self._torsion_basis()

        # 4. the psi(N) cyclic kernels
        self.kernels = self._cyclic_kernels()
        if len(self.kernels) != self.psi:
            raise ArithmeticError("found %d cyclic kernels, expected psi(N) = %d"
                                  % (len(self.kernels), self.psi))

    # ------------------------------------------------------------- set-up

    def _root_of_P(self, F, emb, root_index):
        PF = PolynomialRing(F, 'x')(emb.poly(self.P))
        roots = sorted(PF.roots(multiplicities=False), key=str)
        return roots[root_index % len(roots)]

    def reduce(self, a):
        r"""
        The image in `\GF{P} \subseteq E` of `a \in A`, i.e. `a(\theta_P)`.
        """
        return _horner(self.emb.poly(self.A(a)), self.theta, self.E.zero())

    def _torsion_basis(self):
        E, p, q, e = self.E, self.p, self.q, self.e
        M = E.degree()
        z = E.gen()
        rows = []
        zi = E.one()
        for _ in range(M):
            val, x = E.zero(), zi
            for c in self.phiN:                   # phibar_N(z^i)
                if c:
                    val += c * x
                x = x ** q
            rows.append(_coords(val, E))
            zi = zi * z
        ker = matrix(GF(p), rows).left_kernel().basis()
        if len(ker) != 2 * e * self.d:
            raise ArithmeticError("the N-torsion is not contained in E")
        zpow = [z ** i for i in range(M)]
        points = []
        for v in ker:
            w = E.zero()
            for a, zi in zip(v, zpow):
                if a:
                    w += int(a) * zi
            points.append(w)
        # an F_q-basis out of the F_p-basis: F_q-span(B) = F_p-span(y^a b)
        ypow = [self.emb(self.Fq.gen() ** a) for a in range(e)] if e > 1 else [E.one()]
        basis, span = [], []
        for w in points:
            cand = span + [_coords(w, E)]
            if matrix(GF(p), cand).rank() == len(cand):
                basis.append(w)
                span += [_coords(ya * w, E) for ya in ypow]
        assert len(basis) == 2 * self.d
        return basis

    def T_action(self, w):
        r"""
        `\bar\varphi_T(w) = \theta_P w + \bar g w^q + \bar\Delta w^{q^2}`.
        """
        q = self.q
        wq = w ** q
        return self.theta * w + self.g * wq + self.Delta * wq ** q

    def action(self, a, w):
        r"""
        `\bar\varphi_a(w)` for `a \in A`.
        """
        out, cur = self.E.zero(), w
        for c in self.emb.poly(a):
            if c:
                out += c * cur
            cur = self.T_action(cur)
        return out

    def _span(self, vectors):
        r"""
        All `\GF{q}`-linear combinations of ``vectors``, as pairs
        (coordinate tuple, element).
        """
        out = [((), self.E.zero())]
        for b in vectors:
            out = [(co + (c,), x + c * b) for co, x in out for c in self._scalars]
        return out

    def _cyclic_kernels(self):
        d = self.d
        cofactors = [self.N // ell for ell, _ in self.N.factor()]
        covered, kernels = set(), []
        for coords, w in self._span(self.basis):
            if not w or w in covered:
                continue
            if any(not self.action(c, w) for c in cofactors):
                continue                        # the annihilator of w is not (N)
            flag = [w]
            for _ in range(d - 1):
                flag.append(self.T_action(flag[-1]))
            covered.update(x for _, x in self._span(flag))
            kernels.append(CyclicKernel(w, coords, flag))
        return kernels

    # ----------------------------------------------------------- isogenies

    def kernel_polynomial(self, C):
        r"""
        The coefficients `[u_0, \dots, u_d]` (`u_d = 1`, `d = \deg N`) of the
        kernel polynomial `u_C = \prod_{c\in C}(x - c) = \sum u_i\tau^i`, by the
        subspace recursion `e_{V+\GF{q}v} = e_V^q - e_V(v)^{q-1}e_V`.
        """
        q, E = self.q, self.E
        u = [E.one()]
        for w in C.flag:
            c, x = E.zero(), w
            for a in u:
                c += a * x
                x = x ** q
            c = c ** (q - 1)
            u = [(u[i - 1] ** q if i >= 1 else E.zero())
                 - (c * u[i] if i < len(u) else E.zero())
                 for i in range(len(u) + 1)]
        return u

    def quotient(self, C):
        r"""
        The coefficients `(\bar g', \bar\Delta')` of `\bar\varphi/\bar C`,
        from the top coefficients of `u_C\bar\varphi_T = (\bar\varphi/\bar C)_T u_C`:
        `\Delta' = \Delta^{q^d}` and
        `g' = g^{q^d} + u_{d-1}\Delta^{q^{d-1}} - \Delta^{q^d}u_{d-1}^{q^2}`.
        """
        q, d = self.q, self.d
        u = self.kernel_polynomial(C)
        Dp = self.Delta ** (q ** d)
        gp = self.g ** (q ** d) + u[d - 1] * self.Delta ** (q ** (d - 1)) \
            - Dp * u[d - 1] ** (q ** 2)
        return gp, Dp

    def quotient_bottom(self, C):
        r"""
        The coefficient `\bar g'` of `\bar\varphi/\bar C` computed from the
        *bottom* of `u_C\bar\varphi_T = (\bar\varphi/\bar C)_Tu_C`:
        `g' = u_0^{1-q}g + u_0^{-q}u_1(\theta_P^q - \theta_P)`
        (used as a consistency check against :meth:`quotient`).
        """
        q = self.q
        u = self.kernel_polynomial(C)
        return u[0] ** (1 - q) * self.g \
            + u[0] ** (-q) * u[1] * (self.theta ** q - self.theta)

    def isogenous_j_invariants(self):
        r"""
        The list of `j(\bar\varphi/\bar C) \in E`, over the `\psi(N)` cyclic
        kernels; by the product formula this is the multiset of roots of
        `\Phi_N(X, j(\bar\varphi))` modulo `P`.
        """
        out = []
        for C in self.kernels:
            gp, Dp = self.quotient(C)
            out.append(gp ** (self.q + 1) / Dp)
        return out

    def count_isogenous(self, J):
        r"""
        The number of cyclic kernels `\bar C` with `j(\bar\varphi/\bar C) = \bar J`
        for `J \in A`: this is `C_{J,\,j(\varphi)}(N,P)`.
        """
        Jbar = self.reduce(J)
        return sum(1 for j in self.isogenous_j_invariants() if j == Jbar)

    def S(self, C):
        r"""
        The residue `\bar S_C = \bar u_1/\bar u_0 = \sum_{0\ne c\in C}c^{1-q}`
        of the kernel `C`.
        """
        u = self.kernel_polynomial(C)
        return u[1] / u[0]


def reduced_module_with_j(N, P, J):
    r"""
    A :class:`ReducedDrinfeldModule` at `P` whose `j`-invariant is the
    reduction of `J \in A`: `T \mapsto \theta_P + \bar J\tau + \bar J^q\tau^2`
    if `P \nmid J`, and `\phi^0 : T \mapsto \theta_P + \tau^2` otherwise.
    """
    A = N.parent()
    J = A(J) % A(P)
    if J == 0:
        return ReducedDrinfeldModule(N, P)
    return ReducedDrinfeldModule(N, P, g=J, Delta=J ** N.base_ring().cardinality())


def is_supersingular(P, g=0, Delta=1):
    r"""
    Whether the reduction at the monic prime `P` of
    `\varphi_T = T + g\tau + \Delta\tau^2` (`g, \Delta \in A`, `P\nmid\Delta`)
    is supersingular, i.e. whether `\bar\varphi_P` is purely inseparable
    (`\bar\varphi_P = c\,\tau^{2\deg P}`).

    EXAMPLES:

    `j = 0` is supersingular exactly at the primes of odd degree::

        sage: from drinfeld_modpoly import is_supersingular
        sage: A.<T> = GF(3)[]
        sage: [is_supersingular(P) for P in (T, T^2 + 1, T^3 + 2*T + 1)]
        [True, False, True]
    """
    A = P.parent()
    Fq = A.base_ring()
    q = ZZ(Fq.cardinality())
    P, g, Delta = A(P), A(g), A(Delta)
    dP = P.degree()
    FP = _extension_field(ZZ(Fq.characteristic()), ZZ(Fq.degree()) * dP, 'b')
    emb = FieldEmbedding(Fq, FP)
    theta = PolynomialRing(FP, 'x')(emb.poly(P)).roots(multiplicities=False)[0]
    phiT = [theta, _horner(emb.poly(g), theta, FP.zero()),
            _horner(emb.poly(Delta), theta, FP.zero())]
    if not phiT[2]:
        raise ValueError("bad reduction: P divides Delta")
    phiP = skew_evaluate(emb.poly(P), phiT, q)
    return all(not c for c in phiP[:2 * dP])


def supersingular_j_invariants(P):
    r"""
    The supersingular `j`-invariants in characteristic `P` that lie in
    `\GF{P} = A/P`, as polynomials of degree `< \deg P`.

    For `\deg P \le 2` there is exactly one supersingular `j`-invariant, and
    it lies in `\GF{P}` (Propositions 2.3 and 2.4 of the paper).

    EXAMPLES::

        sage: from drinfeld_modpoly import supersingular_j_invariants
        sage: A.<T> = GF(3)[]
        sage: supersingular_j_invariants(T^2 + T + 2)
        [T + 2]
        sage: supersingular_j_invariants(T + 1)
        [0]
    """
    A = P.parent()
    q = ZZ(A.base_ring().cardinality())
    out = []
    for J in A.polynomials(max_degree=P.degree() - 1):
        if J == 0:
            ss = is_supersingular(P)
        else:
            ss = is_supersingular(P, g=J, Delta=(J ** q) % P)
        if ss:
            out.append(J)
    return sorted(out)
