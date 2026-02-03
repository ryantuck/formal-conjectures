# Erdos Problem 131 Formalization Log

## Problem Description

Erdos Problem 131 asks for the size of the largest subset $A \subseteq \{1, \dots, N\}$ such that no element divides the sum of any non-empty subset of the others.
Conjecture: $F(N) > N^{1/2-o(1)}$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/131.lean`
- **Theorem Name:** `Erdos131.erdos_131`
- **Status:** Disproved (Pham and Zakharov).

We defined:
- `IsDivSumFree`
- `F(N)` (noncomputable)

The theorem states the conjecture is false.

## References

- [PhZa24] Pham, H. and Zakharov, D., "On a problem of Erdős about subset sums", arXiv:2401.03234 (2024).
- [ELRSS99] Erdős, P. et al., "On the divisibility of subset sums", Discrete Math. (1999), 35-43.
