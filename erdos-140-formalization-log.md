# Erdos Problem 140 Formalization Log

## Problem Description

Erdos Problem 140 asks for the upper bound of $r_3(N)$, the size of the largest subset of $\{1, \dots, N\}$ free of 3-term arithmetic progressions.
Conjecture: $r_3(N) \ll N/(\log N)^C$ for every $C>0$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/140.lean`
- **Theorem Name:** `Erdos140.erdos_140`
- **Status:** Solved (Kelley and Meka).

We defined:
- `IsAP3Free`
- `r3` (noncomputable)

The theorem states the bound holds.

## References

- [KeMe23] Kelley, Z. and Meka, R., "Strong bounds for 3-progressions", arXiv:2302.05537 (2023).
