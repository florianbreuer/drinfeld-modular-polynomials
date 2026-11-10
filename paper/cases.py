# -*- coding: utf-8 -*-
r"""
The data set of Section 5 of the paper, and helpers shared by the scripts in
this directory.
"""
from __future__ import print_function

import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if REPO not in sys.path:
    sys.path.insert(0, REPO)

from drinfeld_modpoly.database import base_ring, level_tag, load_polynomial
from drinfeld_modpoly.util import monic_polynomials

DATA = os.path.join(REPO, "data")

# Models of the non-prime fields: F_4 = F_2[y]/(y^2+y+1), F_9 = F_3[y]/(y^2+1).
# (In F_9 this makes y an element of order 4, as in the computations reported
# in the paper: the base place "T + y" of Section 5.1 refers to this y.)
FIELD_MODULI = {(2, 2): [1, 1, 1], (3, 2): [1, 0, 1]}

# The 20 levels for which the paper computes the full Phi_N(X,Y):
# (p, e, coefficients of N in F_p, constant term first).
LEVELS = [
    (2, 1, [0, 1]),            # T
    (2, 1, [1, 1]),            # T + 1
    (2, 1, [0, 0, 1]),         # T^2
    (2, 1, [0, 1, 1]),         # T(T + 1)
    (2, 1, [1, 1, 1]),         # T^2 + T + 1
    (2, 1, [0, 0, 0, 1]),      # T^3
    (2, 1, [1, 1, 0, 1]),      # T^3 + T + 1
    (3, 1, [0, 1]),            # T
    (3, 1, [1, 1]),            # T + 1
    (3, 1, [2, 1]),            # T + 2
    (3, 1, [0, 1, 1]),         # T(T + 1)
    (3, 1, [1, 2, 1]),         # (T + 1)^2
    (3, 1, [1, 1, 1]),         # (T + 2)^2
    (3, 1, [1, 0, 1]),         # T^2 + 1
    (3, 1, [2, 0, 1]),         # T^2 + 2
    (3, 1, [2, 1, 1]),         # T^2 + T + 2
    (3, 1, [2, 2, 1]),         # T^2 + 2T + 2
    (2, 2, [0, 1]),            # T   (q = 4)
    (5, 1, [0, 1]),            # T   (q = 5)
    (3, 2, [0, 1]),            # T   (q = 9)
]


def ring(p, e=1):
    r"""The ring A = F_q[T], q = p^e, in the model used for the data set."""
    return base_ring(p, e, FIELD_MODULI.get((p, e)))


def levels():
    r"""The 20 levels of the paper, as polynomials."""
    return [ring(p, e)(c) for p, e, c in LEVELS]


def levels_at_zero():
    r"""The 24 monic N of degree 3 and 4 over F_2 (for Phi_N(X,0))."""
    A = ring(2)
    return [N for d in (3, 4) for N in monic_polynomials(A, d)]


def path(N, at_zero=False):
    return os.path.join(DATA, "phi_at_zero" if at_zero else "phi", level_tag(N) + ".json")


def load(N, at_zero=False):
    r"""(Phi, record) for a level of the data set."""
    Phi, N0, data = load_polynomial(path(N, at_zero))
    assert N0 == N, "data file %s contains another level" % path(N, at_zero)
    return Phi, data


class Dataset(list):
    r"""
    The list of triples (N, Phi_N, record) for the 20 levels of the paper.

    (Polynomials over different fields can compare equal -- T over F_2 and T
    over F_4, say -- so levels are looked up by ring *and* value.)
    """
    def __init__(self):
        list.__init__(self, [(N,) + load(N) for N in levels()])

    def has(self, N):
        return any(M.parent() is N.parent() and M == N for M, _, _ in self)

    def phi(self, N):
        for M, Phi, _ in self:
            if M.parent() is N.parent() and M == N:
                return Phi
        raise KeyError("level %s is not in the data set" % N)

    def over(self, A):
        r"""The levels of the data set in the ring A."""
        return [M for M, _, _ in self if M.parent() is A]


class Report(object):
    r"""Collects the outcome of the checks and prints a readable log."""
    def __init__(self, log_path=None):
        self.passed = 0
        self.failures = []
        self._log = open(log_path, "w") if log_path else None

    def say(self, text=""):
        print(text)
        sys.stdout.flush()
        if self._log:
            self._log.write(text + "\n")
            self._log.flush()

    def section(self, title):
        self.say()
        self.say(title)
        self.say("-" * len(title))

    def check(self, label, ok):
        if ok:
            self.passed += 1
        else:
            self.failures.append(label)
            self.say("   *** FAIL: " + label)
        return bool(ok)

    def finish(self):
        self.say()
        self.say("=" * 72)
        self.say("%d checks passed, %d failed" % (self.passed, len(self.failures)))
        for f in self.failures:
            self.say("   FAILED: " + f)
        if self._log:
            self._log.close()
        return 0 if not self.failures else 1
