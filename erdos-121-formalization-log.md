# Erdos Problem 121 Formalization Log

## Problem Description

Erdos Problem 121 asks if $F_{2k+1}(N) = (1-o(1))N$, where $F_k(N)$ is the size of the largest subset of $\{1, \dots, N\}$ containing no $k$ distinct elements whose product is a square.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/121.lean`
- **Theorem Name:** `Erdos121.erdos_121`
- **Status:** Disproved by Tao [Ta24].

We defined:
- `NoProductKIsSquare`
- `F` (noncomputable)

The theorem states the equivalence of the answer being false with the existence of counterexamples for $k \ge 2$ (since $2k+1 \ge 5$).

## References

- [Ta24] Tao, T., "On the Erdős-Sós-Sárközy conjecture on the size of subsets of integers with no k elements multiplying to a square". arXiv:2408.01804 (2024).
- [ESS95] Erdős, P., Sárközy, A., and Sós, V. T., "On product representations of powers, I", European J. Combin. (1995), 567-588.
