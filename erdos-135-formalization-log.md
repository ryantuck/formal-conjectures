# Erdos Problem 135 Formalization Log

## Problem Description

Erdos Problem 135 asks if a set of $n$ points in the plane where every 4 points determine at least 5 distances must determine $\gg n^2$ distances.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/135.lean`
- **Theorem Name:** `Erdos135.erdos_135`
- **Status:** Disproved (Tao).

We defined:
- `NumDistances'`
- `FourPointsFiveDistances`

The theorem states the conjecture is false.

## References

- [Ta24c] Tao, T., "A counterexample to an Erdős problem on the number of distances", arXiv:2409.07921 (2024).
