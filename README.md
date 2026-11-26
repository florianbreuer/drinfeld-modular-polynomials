# Drinfeld modular polynomials

SageMath code to compute the Drinfeld modular polynomials Φ_N(X, Y) ∈ A[X, Y],
A = F_q[T], exactly, for an arbitrary level N and an arbitrary prime power q —
together with scripts that verify every numerical claim of the paper

> F. Breuer and F. Pazuki, *Divisibility of the coefficients of Drinfeld modular
> polynomials*.

Φ_N is the polynomial that vanishes exactly at the pairs (j(φ), j(φ′)) of
j-invariants of rank 2 Drinfeld A-modules linked by a cyclic isogeny of degree N.
It is symmetric, monic, and of degree ψ(N) = |N| ∏_{P | N} (1 + 1/|P|) in each variable.

## Quick start

No installation is needed: clone the repository and start `sage` in its root
directory. The only requirement is SageMath (see [Compatibility](#compatibility)).

For a guided tour, open the notebook
[`DrinfeldModularPolynomials.ipynb`](DrinfeldModularPolynomials.ipynb). It
computes one modular polynomial from scratch, displays Table 1 of the paper with
the predicted factors in bold, and then illustrates each result of the paper on
the polynomials stored in `data/`. It is saved with its output, so it can be read
without running it; to run it (about a minute), start `sage -n jupyter` in the
root directory.

```python
sage: from drinfeld_modpoly import *
sage: A.<T> = GF(2)[]
sage: Phi = drinfeld_modular_polynomial(T^2 + T + 1)
sage: X, Y = Phi.parent().gens()
sage: Phi.degree(X), height(Phi)
(5, 24)
sage: Phi.monomial_coefficient(X^2).factor()         # a_(2,0), cf. Table 1 of the paper
T^9 * (T + 1)^9 * (T^2 + T + 1)^3
```

Any prime power q, and levels that are composite or not squarefree, work the
same way:

```python
sage: A.<T> = GF(9, 'y')[]
sage: Phi = drinfeld_modular_polynomial(T)            # degree 10, height 810; ~ 30 seconds
sage: A.<T> = GF(2)[]
sage: Phi = drinfeld_modular_polynomial(T^2 * (T + 1), verbose=True)   # degree 18
```

The univariate specialization Φ_N(X, 0) is much cheaper and has its own function:

```python
sage: A.<T> = GF(2)[]
sage: f = drinfeld_modular_polynomial_at_zero(T^4 + T^3 + 1)     # degree 17, ~ 1 second
```

From the shell, `examples/compute.py` prints the coefficients in factored form,
with the factor predicted by Theorem 1.2(1) of the paper in brackets:

```
$ sage examples/compute.py 2 "T^2+T+1"
  a_(1,1) = [T^9 * (T + 1)^9] * T^2 * (T + 1)^2
  a_(2,0) = [T^9 * (T + 1)^9] * (T^2 + T + 1)^3
  a_(2,1) = [T^6 * (T + 1)^6] * (T^2 + T + 1) * (T^4 + T + 1)
  ...
```

### Main functions

| function | |
|---|---|
| `drinfeld_modular_polynomial(N, place=None)` | Φ_N(X, Y) ∈ A[X, Y] |
| `drinfeld_modular_polynomial_at_zero(N, place=None)` | Φ_N(X, 0) ∈ A[X] |
| `psi(N)`, `height_bound(N)`, `height(Phi)` | degree, proven height bound, height |
| `ReducedDrinfeldModule(N, P, g, Delta)` | N-torsion, cyclic kernels and isogenous j-invariants of a Drinfeld module in characteristic P |
| `analysis.shifted(Phi, J1, J2)` | Φ(X + J₁, Y + J₂) |
| `analysis.C_J(Phi, J1, J2, P)` | C_{J₁,J₂}(N, P) = ord_X(Φ_N(X + J₁, J₂) mod P) |
| `analysis.n_opt(Phi, P, C)` | the best constant n with v_P(a_{m,n}) ≥ n (C − m − n) |
| `special.bassa_beelen_phi_T(A)` | the closed form of Bassa–Beelen for Φ_T |
| `database.load_level(N)`, `database.load_all()` | polynomials from `data/` |
| `display.CoefficientTable(Phi, bounds)` | the coefficients in factored form, predicted factors set apart |

## Is the output correct?

Yes, provably. The algorithm (Algorithm 1 of the paper) takes as input an upper
bound h for the height of Φ_N — the largest T-degree of a coefficient — and
returns the exact Φ_N as soon as its working precision exceeds an explicit
function of h (Proposition 5.1 of the paper). The code uses the bound

    h(Φ_N) ≤ (q² − 1)/2 · ψ(N) · (deg N − 2λ_N + B_q),
    λ_N = Σ_{P^n ‖ N} (|P|^n − 1)/(|P|^{n−1}(|P|² − 1)) · deg P,
    B_q = 4 + (5q³ − q² − q + 1)/(q(q + 1)(q − 1)²)      (= 59/6 for q = 2),

proved by Breuer–Pazuki–Ran (arXiv:2410.11132v3, Thm. 1.1), and 12 digits of
precision more than required. On top of that, every run checks that the spare
digits of every coefficient vanish, that all residues lie in the right subfield,
that no coefficient exceeds the height bound, and that the result is monic and
symmetric; any failure raises an `ArithmeticError`.

## Verifying the paper

```
sage tests/run_tests.py              # self-tests of the package                 (~ 30 s)
sage paper/verify_paper.py           # every numerical claim of the paper        (~ 20 s)
sage paper/recompute.py all          # recompute all 44 polynomials from scratch (~ 4 min)
sage paper/recompute.py places-all   # ... and again at other base places        (~ 2 min)
```

(`recompute.py quick` and `recompute.py places` are shorter versions of the last
two, about 10 s and 1 min.)

`paper/verify_paper.py` works from the certified polynomials stored in `data/`
and checks, section by section:

| | claims | where in the paper |
|---|---|---|
| A | the 20 polynomials Φ_N are monic and symmetric, satisfy the Kronecker congruence for prime N, have height below the proven bound (by a factor between 2.3 and 5.9) and equal to q²(q+1) at level T; they are compatible with the automorphisms σ: T ↦ aT + b of A, i.e. Φ_{σ(N)}(X, Y) = a^{−ψ(N)} σ(Φ_N)(aX, aY) (58 pairs (N, σ) within the data set) | §5, §5.1, §4 |
| B | Table 1: all coefficients of Φ_{T²+T+1} for q = 2, in factored form | §5.2 |
| C | Theorem 1.2(1) at all 44 pairs (N, P) with deg P = 1: C₀(N, P) = ψ(N), the bound holds, and n_opt = q + 1 in every case; the two cases where the lowest coefficient is not a witness; the residues S_C of the kernels, Lemma 3.7, and the formula v_P(j(φ⁰/C)) = (q+1)(1 + v_P(S_C)) | §5.3 |
| D | primes of degree 2 (ordinary: C₀(N, P) = C₀(N, 0)) and of degree 3; Φ_N(X, 0) for all 24 levels of degree 3 and 4 over F₂: supersingular excess at 20 of them, always a multiple of q + 1, with an independent recount of C₀(N, P) in characteristic P (42 cases); Theorem 1.2(2) at the excess prime of Φ_{T³} | §5.4 |
| E | the singular moduli J_s and J_c in closed form; Proposition 4.5; the table for J_s (q = 3, nine levels); Theorem 4.1 and Corollary 4.3 for 36 pairs (J, N) with J not a singular modulus, with the constants 4/3, 7/3, 5/4, 5/2, 13/4 attained; Corollary 4.6 for J_c (q = 2, 3); Proposition 2.4 and Remarks 2.5, 4.4 | §4, §5.5 |
| F | Φ_T against the closed form of Bassa–Beelen (q = 2, 3, 4, 5, 9); the examples of Caranay–Greenberg–Scheidler; Res_Z(Φ_T(X, Z), Φ_{T+1}(Z, Y)) = Φ_{T(T+1)}(X, Y) for q = 2 | §5.1 |

`paper/recompute.py` recomputes the polynomials with the proven height bound and
compares them, coefficient by coefficient, with `data/`. The output of a complete
run of these scripts with SageMath 9.3 is in `paper/logs/`.

(Theorem, section and table numbers are those of the version of the paper of November 2026.)

## The data

`data/phi/` contains Φ_N(X, Y) for the 20 levels of the paper,

- q = 2: T, T+1, T², T(T+1), T²+T+1, T³, T³+T+1;
- q = 3: T, T+1, T+2, T(T+1), (T+1)², (T+2)², T²+1, T²+2, T²+T+2, T²+2T+2;
- q = 4, 5, 9: T;

and `data/phi_at_zero/` contains Φ_N(X, 0) for all 24 monic N of degree 3 and 4
over F₂. The files are JSON; the format is described in
`drinfeld_modpoly/database.py`, and `database.load_polynomial` reads them.

All files were produced by `sage paper/recompute.py all --write`. The 20
polynomials Φ_N(X, Y), and 9 of the Φ_N(X, 0), have also been compared with the
output of an independent pure-Python implementation of the same algorithm (not
included in this repository): they are identical.

## The algorithm in brief

Fix a monic prime P ∤ N of degree d_P (by default: of smallest possible degree)
and work in the finite ring R = E[π]/(π^K), where E is a finite field containing
A/P and the N-torsion of the reduction of φ⁰: T ↦ T + τ² (the Drinfeld module
with j = 0), and π stands for P.

1. For ψ(N) + 1 values ε_s ∈ E* with pairwise distinct (q+1)-st powers, deform
   φ⁰ to φ^s: T ↦ t + ε_s π τ + τ², of j-invariant y_s = (ε_s π)^{q+1}.
2. Lift the N-torsion from E to R by Newton iteration; for each of the ψ(N)
   cyclic kernels C compute its kernel polynomial and, from it, j(φ^s/C).
3. Φ_N(X, y_s) = ∏_C (X − j(φ^s/C)); interpolate in Y. This costs exactly
   (q+1)ψ(N) digits of precision.
4. Read each coefficient off its P-adic expansion.

No Chinese remaindering is needed, and the nodes of the interpolation are the
very deformations on which the proofs of the paper rest. The implementation
follows Algorithm 1 of the paper with two shortcuts, both immediate from it:
only an F_q-basis of the torsion is lifted (the lifting map is F_q-linear), and
since y_s = ε_s^{q+1} π^{q+1}, the interpolation is done by inverting a
Vandermonde matrix over the field E, followed by exact divisions by powers of π.

Timings with SageMath 9.3 on a laptop:

| q | N | ψ(N) | place | precision K | E | time |
|---|---|---|---|---|---|---|
| 2 | T²+T+1 | 5 | T | 109 | F_{2^6} | 0.5 s |
| 2 | T(T+1) | 9 | T²+T+1 | 110 | F_{2^6} | 2 s |
| 2 | T³ | 12 | T+1 | 258 | F_{2^8} | 10 s |
| 3 | T²+1 | 10 | T | 379 | F_{3^8} | 8 s |
| 3 | T(T+1) | 16 | T+2 | 561 | F_{3^4} | 15 s |
| 4 | T | 5 | T+1 | 272 | F_{2^8} | 0.5 s |
| 5 | T | 6 | T+1 | 473 | F_{5^4} | 1 s |
| 9 | T | 10 | T+1 | 2278 | F_{3^8} | 25 s |

The complete list is in `paper/logs/recompute_all.log`. Each Φ_N(X, 0) for N of
degree 3 or 4 over F₂ (ψ(N) up to 45) takes between 0.3 and 12 seconds.
Some examples beyond the data set of the paper (y denotes a generator of F_q):

| q | N | ψ(N) | place | precision K | E | time |
|---|---|---|---|---|---|---|
| 7 | T | 8 | T+1 | 1146 | F_{7^4} | 7 s |
| 8 | T | 9 | T+1 | 1647 | F_{2^12} | 30 s |
| 8 | T+y | 9 | T+y+1 | 1647 | F_{2^12} | 26 s |
| 2 | T²(T+1) | 18 | T²+T+1 | 217 | F_{2^12} | 40 s |
| 2 | T⁴+T+1 | 17 | T | 403 | F_{2^30} | 3 min |
| 4 | T²+yT+1 | 17 | T | 1045 | F_{2^20} | 3 min |
| 5 | T²+2 | 26 | T+2 | 2379 | F_{5^6} | 6 min |

The cost of the full Φ_N grows roughly like ψ(N)³ multiplications of power series
of length K ≈ h/d_P + (q+1)ψ(N) over E.

## Layout

```
drinfeld_modpoly/        the package
    modular_polynomial.py    Algorithm 1: Φ_N(X, Y) and Φ_N(X, 0)
    reduction.py             Drinfeld modules over finite fields: torsion, kernels, isogenies
    heights.py               ψ(N), λ_N, the proven height bound
    analysis.py              shifts, C_J(N, P), n_opt, Newton polygons, Kronecker congruence
    special.py               J_s, J_c, the Bassa–Beelen closed form
    database.py              JSON input/output
    display.py               factored coefficient tables (text and notebook)
    util.py                  monic primes, valuations
DrinfeldModularPolynomials.ipynb   a guided tour (SageMath kernel)
data/                    the certified polynomials of the paper
paper/                   verify_paper.py, recompute.py, logs/
tests/                   run_tests.py
examples/                compute.py
```

## Compatibility

Developed and tested with SageMath 9.3 (Python 3.7). Only long-standing parts of
the Sage library are used (finite fields, polynomial rings, matrices); in
particular the code does not rely on Sage's `DrinfeldModule` class, which
appeared in Sage 10.0.

## Citing

If you use this code, please cite the paper above (see `CITATION.cff`).

## License

MIT, see `LICENSE`.
