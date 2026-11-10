# -*- coding: utf-8 -*-
r"""
Reading and writing Drinfeld modular polynomials as JSON.

File format (``"format": "drinfeld-modpoly/1"``):

- ``p``, ``e`` -- the base field is `\GF{q}`, `q = p^e`;
- ``Fq_modulus`` -- for `e > 1`, the coefficients (constant term first) of the
  minimal polynomial over `\GF{p}` of the generator `y` of `\GF{q}`;
- ``N`` -- the level, as a list of coefficients, constant term first;
- ``kind`` -- ``"Phi_N(X,Y)"`` or ``"Phi_N(X,0)"``;
- ``coefficients`` -- the nonzero coefficients: a dictionary with keys
  ``"m,n"`` (resp. ``"m"``) for the coefficient of `X^mY^n` (resp. `X^m`),
  each an element of `\GF{q}[T]` given by its list of coefficients, constant
  term first;
- ``psi``, ``height`` and a ``computation`` record (place, precision, height
  bound, running time, software).

An element of `\GF{q}` is an integer in `[0,p)` if `e = 1`, and otherwise the
list `[c_0, \dots, c_{e-1}]` of the coordinates of `\sum_i c_iy^i`.
"""
import json
import os
import re

from sage.all import GF, PolynomialRing, ZZ

from drinfeld_modpoly.reduction import _coords

FORMAT = "drinfeld-modpoly/1"


def base_ring(p, e=1, modulus=None):
    r"""
    The ring `A = \GF{q}[T]`, `q = p^e`, with `\GF{q} = \GF{p}[y]/(\mathrm{modulus})`
    (default modulus: SageMath's default for ``GF(q, 'y')``).
    """
    if e == 1:
        Fq = GF(p)
    elif modulus is None:
        Fq = GF(p ** e, 'y')
    else:
        Fq = GF(p ** e, 'y', modulus=PolynomialRing(GF(p), 'x')(modulus))
    return PolynomialRing(Fq, 'T')


def level_tag(N):
    r"""
    A file-name friendly tag for a level, e.g. ``q3_T2+2T+2`` for
    `N = T^2+2T+2` over `\GF{3}`.
    """
    q = N.base_ring().cardinality()
    s = str(N).replace(' ', '').replace('*', '').replace('^', '')
    return "q%s_%s" % (q, re.sub(r'[^A-Za-z0-9+]', '_', s))


def _elt(c, Fq):
    v = _coords(c, Fq)
    return v[0] if Fq.degree() == 1 else v


def _poly(a):
    Fq = a.base_ring()
    return [_elt(c, Fq) for c in a.list()]


def save_polynomial(path, Phi, N, computation=None):
    r"""
    Write `\Phi_N(X,Y) \in A[X,Y]` or `\Phi_N(X,0) \in A[X]` to ``path``.
    """
    A = N.parent()
    Fq = A.base_ring()
    bivariate = Phi.parent().ngens() == 2
    if bivariate:
        coeffs = dict(("%d,%d" % (k[0], k[1]), _poly(c)) for k, c in Phi.dict().items())
        psi = Phi.degree(Phi.parent().gen(0))
    else:
        coeffs = dict(("%d" % k, _poly(c)) for k, c in Phi.dict().items())
        psi = Phi.degree()
    data = {
        "format": FORMAT,
        "kind": "Phi_N(X,Y)" if bivariate else "Phi_N(X,0)",
        "p": int(Fq.characteristic()),
        "e": int(Fq.degree()),
        "N": _poly(N),
        "N_string": str(N),
        "psi": int(psi),
        "height": int(max(c.degree() for c in Phi.coefficients())),
        "computation": computation or {},
        "coefficients": coeffs,
    }
    if Fq.degree() > 1:
        data["Fq_modulus"] = [int(c) for c in Fq.modulus().list()]
    with open(path, "w") as f:
        json.dump(data, f, sort_keys=True, separators=(",", ":"))
        f.write("\n")


def load_polynomial(path, names=('X', 'Y')):
    r"""
    Read a polynomial written by :func:`save_polynomial`.

    OUTPUT: a triple ``(Phi, N, data)``, where ``Phi`` lies in `A[X,Y]` (or
    `A[X]`), ``N`` is the level and ``data`` is the full JSON record.
    """
    with open(path) as f:
        data = json.load(f)
    if data.get("format") != FORMAT:
        raise ValueError("%s: unknown format %r" % (path, data.get("format")))
    p, e = ZZ(data["p"]), ZZ(data["e"])
    A = base_ring(p, e, data.get("Fq_modulus"))
    Fq = A.base_ring()
    if e == 1:
        elt = Fq
    else:
        ypow = [Fq.gen() ** i for i in range(e)]
        elt = lambda v: sum((Fq(c) * yi for c, yi in zip(v, ypow)), Fq.zero())
    poly = lambda v: A([elt(c) for c in v])
    N = poly(data["N"])
    if data["kind"] == "Phi_N(X,Y)":
        R = PolynomialRing(A, list(names))
        Phi = R(dict((tuple(int(i) for i in k.split(",")), poly(v))
                     for k, v in data["coefficients"].items()))
    else:
        R = PolynomialRing(A, names[0])
        Phi = R(dict((int(k), poly(v)) for k, v in data["coefficients"].items()))
    return Phi, N, data


def data_directory():
    r"""The ``data`` directory shipped with this repository."""
    return os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")


def load_level(N, at_zero=False):
    r"""
    Load `\Phi_N(X,Y)` (or `\Phi_N(X,0)` if ``at_zero``) from the ``data``
    directory, if it is there.  The polynomial is returned over the model of
    `\GF{q}` recorded in the file (for `q = 4, 9` in ``data``:
    `y^2+y+1 = 0`, resp. `y^2 + 1 = 0`).

    EXAMPLES::

        sage: from drinfeld_modpoly.database import load_level
        sage: A.<T> = GF(3)[]
        sage: Phi, data = load_level(T^2 + 1)
        sage: data["psi"], data["height"]
        (10, 108)
    """
    sub = "phi_at_zero" if at_zero else "phi"
    path = os.path.join(data_directory(), sub, level_tag(N) + ".json")
    Phi, N0, data = load_polynomial(path)
    if _poly(N0) != _poly(N):
        raise ValueError("%s contains a different level" % path)
    return Phi, data


def load_all(at_zero=False):
    r"""
    Load every polynomial of the ``data`` directory.

    OUTPUT: a list of triples ``(N, Phi, data)``, ordered by `q`, then by the
    degree of `N`, then by the coefficients of `N`.

    EXAMPLES::

        sage: from drinfeld_modpoly.database import load_all
        sage: len(load_all()), len(load_all(at_zero=True))
        (20, 24)
        sage: [N for N, _, _ in load_all() if N.base_ring().cardinality() == 2]
        [T, T + 1, T^2, T^2 + T, T^2 + T + 1, T^3, T^3 + T + 1]
    """
    folder = os.path.join(data_directory(), "phi_at_zero" if at_zero else "phi")
    out = []
    for name in sorted(os.listdir(folder)):
        if name.endswith(".json"):
            Phi, N, data = load_polynomial(os.path.join(folder, name))
            out.append((N, Phi, data))
    key = lambda item: (int(item[0].base_ring().cardinality()), int(item[0].degree()),
                        str(_poly(item[0])[::-1]))
    return sorted(out, key=key)
