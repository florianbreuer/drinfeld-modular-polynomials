# -*- coding: utf-8 -*-
r"""
Readable output: coefficients in factored form, and small tables.

The objects defined here print as plain text in a terminal and as typeset
mathematics, resp. an HTML table, in a Jupyter notebook.
"""
from sage.all import ZZ, QQ, latex, ceil

from drinfeld_modpoly.util import valuation
from drinfeld_modpoly.analysis import coefficient_dict


def _factor_strings(a, tex, bare=True):
    r"""The factors of a nonzero `a \in A` as a list of strings."""
    F = a.factor()
    Fq = a.base_ring()
    u = Fq(F.unit())
    show = (lambda x: str(latex(x))) if tex else str
    primes = sorted(F, key=lambda fk: (fk[0].degree(), str(fk[0])))
    if bare and u == 1 and len(primes) == 1 and primes[0][1] == 1:
        return [show(primes[0][0])]                 # a prime, standing alone
    parts = []
    if u != 1:
        s = show(u)
        parts.append("(%s)" % s if ("+" in s or " " in s) else s)
    for f, k in primes:
        s = show(f)
        if not f.is_term():
            s = "(%s)" % s
        if k > 1:
            s += ("^{%d}" if tex else "^%d") % k
        parts.append(s)
    return parts


def factored(a, bare=True):
    r"""
    A nonzero element of `A` as a product of prime powers, as a string.
    With ``bare=False`` a prime is put in parentheses, so that the result can
    be used as a factor of a longer product.

    EXAMPLES::

        sage: from drinfeld_modpoly.display import factored
        sage: A.<T> = GF(3)[]
        sage: factored(2*T^2*(T + 1)^3*(T^2 + 1))
        '2 * T^2 * (T + 1)^3 * (T^2 + 1)'
        sage: factored(A(1))
        '1'
    """
    return " * ".join(_factor_strings(a, False, bare)) or "1"


def factored_latex(a, bare=True):
    r"""The same as :func:`factored`, in LaTeX."""
    return " ".join(_factor_strings(a, True, bare)) or "1"


def _escape(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


class Table(object):
    r"""
    A small table of strings: aligned text in a terminal, HTML in a notebook.

    EXAMPLES::

        sage: from drinfeld_modpoly.display import Table
        sage: Table([[2, "T + 1", 3], [3, "T^2 + 1", 10]], header=["q", "N", "psi"])
        q  N        psi
        -  -------  ---
        2  T + 1    3
        3  T^2 + 1  10
    """
    def __init__(self, rows, header=None, caption=None):
        self.rows = [[str(c) for c in row] for row in rows]
        self.header = None if header is None else [str(c) for c in header]
        self.caption = caption

    def __repr__(self):
        rows = ([self.header] if self.header else []) + self.rows
        width = [max(len(r[i]) for r in rows) for i in range(len(rows[0]))]
        line = lambda r: "  ".join(c.ljust(w) for c, w in zip(r, width)).rstrip()
        out = [self.caption] if self.caption else []
        if self.header:
            out += [line(self.header), "  ".join("-" * w for w in width)]
        return "\n".join(out + [line(r) for r in self.rows])

    def _repr_html_(self):
        out = ["<table>"]
        if self.caption:
            out.append("<caption>%s</caption>" % _escape(self.caption))
        if self.header:
            out.append("<tr>%s</tr>" % "".join(
                '<th style="text-align:left">%s</th>' % _escape(c) for c in self.header))
        for r in self.rows:
            out.append("<tr>%s</tr>" % "".join(
                '<td style="text-align:left">%s</td>' % _escape(c) for c in r))
        return "\n".join(out + ["</table>"])


class CoefficientTable(object):
    r"""
    The coefficients `a_{m,n}` of `\Phi(X,Y) = \sum a_{m,n}X^mY^n` in factored
    form, with the factors predicted by a divisibility theorem set apart:
    in brackets in plain text, in bold in a notebook.

    INPUT:

    - ``Phi`` -- an element of `A[X,Y]`
    - ``bounds`` -- a dictionary ``{P: (C, n)}``: for the prime `P`, the
      theorem being illustrated asserts `v_P(a_{m,n}) \ge n\,(C - m - n)`
      whenever `m + n < C`; the predicted factor of `a_{m,n}` is then
      `\prod_P P^{\lceil n(C-m-n)\rceil}`.  A ``ValueError`` is raised if a
      coefficient is not divisible by its predicted factor.
    - ``max_rows`` -- (default: 60) show at most this many coefficients

    If `\Phi` is symmetric, only the `a_{m,n}` with `m \ge n` are listed.

    EXAMPLES:

    Theorem 1.2(1) of the paper for `\Phi_{T+1}`, `q = 2`, at the prime `T`::

        sage: from drinfeld_modpoly import drinfeld_modular_polynomial
        sage: from drinfeld_modpoly.display import CoefficientTable
        sage: A.<T> = GF(2)[]
        sage: Phi = drinfeld_modular_polynomial(T + 1)
        sage: CoefficientTable(Phi, bounds={T: (3, 3)})
        a_(0,0) = [T^9] * (T + 1)^3
        a_(1,0) = [T^6] * (T + 1)^2
        a_(1,1) = [T^3] * (T^2 + T + 1)
        a_(2,0) = [T^3] * (T + 1)
        a_(2,1) = T + 1
        a_(2,2) = 1
        a_(3,0) = 1
        zero: a_(3,1), a_(3,2), a_(3,3)
    """
    def __init__(self, Phi, bounds=None, max_rows=60):
        self.A = Phi.parent().base_ring()
        d = coefficient_dict(Phi)
        self.symmetric = all(d.get((n, m)) == a for (m, n), a in d.items())
        dx = max(m for m, _ in d)
        dy = max(n for _, n in d)
        self.bounds = dict((self.A(P), (ZZ(C), QQ(c))) for P, (C, c) in (bounds or {}).items())
        self.entries, self.zeros = [], []
        for m in range(dx + 1):
            for n in range((m if self.symmetric else dy) + 1):
                a = d.get((m, n))
                if a is None:
                    self.zeros.append((m, n))
                    continue
                pred = self.A.one()
                for P, (C, c) in sorted(self.bounds.items()):
                    k = ceil(c * (C - m - n))
                    if k > 0:
                        if valuation(a, P) < k:
                            raise ValueError("a_(%d,%d) is not divisible by (%s)^%d"
                                             % (m, n, P, k))
                        pred *= P ** k
                self.entries.append((m, n, pred, a // pred))
        self.max_rows = max_rows

    def _shown(self):
        return self.entries[:self.max_rows], len(self.entries) > self.max_rows

    def __repr__(self):
        shown, more = self._shown()
        out = []
        for m, n, pred, rest in shown:
            if pred == 1:
                txt = factored(rest)
            else:
                txt = "[%s]" % factored(pred)
                if rest != 1:
                    txt += " * " + factored(rest, bare=False)
            out.append("a_(%d,%d) = %s" % (m, n, txt))
        if more:
            out.append("... (%d more)" % (len(self.entries) - self.max_rows))
        if self.zeros:
            out.append("zero: " + ", ".join("a_(%d,%d)" % mn for mn in self.zeros))
        return "\n".join(out)

    def _repr_latex_(self):
        shown, more = self._shown()
        rows = []
        for m, n, pred, rest in shown:
            if pred == 1:
                txt = factored_latex(rest)
            else:
                txt = r"\mathbf{%s}" % factored_latex(pred) \
                    + ("" if rest == 1 else r" \cdot " + factored_latex(rest, bare=False))
            rows.append(r"a_{%d,%d} &=& %s" % (m, n, txt))
        if more:
            rows.append(r"&\vdots&")
        out = r"$$\begin{array}{rcl}" + r" \\ ".join(rows) + r"\end{array}$$"
        if self.zeros:
            # the vanishing coefficients, eight to a line, below the table
            names = ["a_{%d,%d}" % mn for mn in self.zeros]
            lines = [" = ".join(names[i:i + 8]) + " =" for i in range(0, len(names), 8)]
            lines[-1] += " 0"
            out += "\n" + r"$$\begin{array}{l}" + r" \\ ".join(lines) + r"\end{array}$$"
        return out
