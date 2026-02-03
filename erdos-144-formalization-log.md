# Erdos Problem 144 Formalization Log

## Problem Description

Erdos Problem 144 asks if the set of integers having two divisors $d_1 < d_2 < c d_1$ has density 1 for any $c > 1$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/144.lean`
- **Theorem Name:** `Erdos144.erdos_144`
- **Status:** Proved (Maier and Tenenbaum).

We defined:
- `HasCloseDivisors`
- `HasNaturalDensity`

The theorem states the density is 1.

## References

- [MaTe84] Maier, H. and Tenenbaum, G., "On the set of divisors of an integer", Invent. Math. (1984), 319-328.
