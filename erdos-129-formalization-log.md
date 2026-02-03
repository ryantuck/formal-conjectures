# Erdos Problem 129 Formalization Log

## Problem Description

Erdos Problem 129 (Erdos and Gyárfás) asks about the growth of $R(n; 3, r)$, defined as the smallest $N$ such that any $r$-coloring of $K_N$ has an $n$-subset missing a monochromatic triangle in at least one color.
The conjecture was $R(n; 3, r) < C^{\sqrt{n}}$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/129.lean`
- **Theorem Name:** `Erdos129.erdos_129`
- **Status:** Disproved (Antonio Girao).

We defined:
- `ContainsKk`
- `Prop129`
- `R` (noncomputable)

The theorem states the conjecture is false.

## References

- [Er97c] Erdős, P., "Some problems I presented at various meetings", Paul Erdős and his Mathematics (1997).
- [Gi] Girao, A., (personal communication/observation mentioned on erdosproblems.com).
