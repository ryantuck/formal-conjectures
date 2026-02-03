# Erdos Problem 148 Formalization Log

## Problem Description

Erdos Problem 148 asks for estimates of $F(k)$, the number of solutions to $\sum_{i=1}^k \frac{1}{n_i} = 1$ with distinct integers.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/148.lean`
- **Theorem Name:** `Erdos148.erdos_148`
- **Status:** Open.

We defined:
- `IsSolution`
- `F(k)` (noncomputable, assumed finite via axiom)

The theorem is a placeholder for the open problem.

## References

- [Ko14] Konyagin, S. V., "On the number of solutions of the equation 1 = 1/n_1 + ... + 1/n_k", Mat. Zametki (2014), 476-480.
- [ElPl21] Elsholtz, C. and Planitzer, S., "The number of solutions to the Erdős-Moser equation", arXiv:2101.05835 (2021).
