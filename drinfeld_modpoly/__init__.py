# -*- coding: utf-8 -*-
r"""
drinfeld_modpoly -- Drinfeld modular polynomials `\Phi_N(X,Y)` for rank 2
Drinfeld `\GF{q}[T]`-modules, computed exactly by deformation at a place.

Companion code to F. Breuer and F. Pazuki, *Divisibility of the coefficients
of Drinfeld modular polynomials*.
"""
from drinfeld_modpoly.heights import psi, lambda_N, B_q, height_bound, height, b_q
from drinfeld_modpoly.util import field_elements, monic_polynomials, monic_primes, valuation
from drinfeld_modpoly.reduction import (ReducedDrinfeldModule, reduced_module_with_j,
                                        is_supersingular, supersingular_j_invariants)
from drinfeld_modpoly.modular_polynomial import (drinfeld_modular_polynomial,
                                                 drinfeld_modular_polynomial_at_zero,
                                                 choose_place, torsion_field_degree)

__version__ = "1.0.0"
