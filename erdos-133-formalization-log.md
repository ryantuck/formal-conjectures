# Erdos Problem 133 Formalization Log

## Problem Description

Erdos Problem 133 asks about the minimal maximum degree $f(n)$ of a triangle-free graph on $n$ vertices with diameter 2.
Specifically, does $f(n)/\sqrt{n} \to \infty$?

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/133.lean`
- **Theorem Name:** `Erdos133.erdos_133`
- **Status:** Disproved.

We defined:
- `HasDiameterTwo`
- `MaxDegree`
- `f(n)` (noncomputable)

The theorem states the limit is false.

## References

- [Al96b] Alon, N., "Minimum degree of graphs with diameter 2", unpublished.
- [Gr] Griffith, "Triangle-free graphs with diameter 2", personal communication.

