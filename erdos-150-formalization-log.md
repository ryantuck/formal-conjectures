# Erdos Problem 150 Formalization Log

## Problem Description

Erdos Problem 150 asks if the maximum number of minimal cuts $c(n)$ satisfies $c(n)^{1/n} \to \alpha < 2$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/150.lean`
- **Theorem Name:** `Erdos150.erdos_150`
- **Status:** Solved (Bradač).

We defined:
- `IsVertexCut`
- `IsMinimalVertexCut`
- `c(n)`

The theorem states the limit property.

## References

- [Br24] Bradač, D., "The number of minimal cuts", arXiv:2401.03234 (2024).
