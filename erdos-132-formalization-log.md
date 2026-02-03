# Erdos Problem 132 Formalization Log

## Problem Description

Erdos Problem 132 asks if every set of $n$ points in the plane determines at least two distances that occur at most $n$ times.
Hopf and Pannowitz proved the maximum distance occurs at most $n$ times.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/132.lean`
- **Theorem Name:** `Erdos132.erdos_132`
- **Status:** Open.

We defined:
- `DistanceCount` (noncomputable)
- `IsRareDistance`

The theorem asks for the existence of at least two rare distances for large $N$.

## References

- [HoPa34] Hopf, H. and Pannowitz, E., "Aufgabe 167", Jber. Deutsch. Math.-Verein. (1934), 114.
- [ErFi95] Erdős, P. and Fishburn, P., "Multiplicities of interpoint distances in finite planar sets", Discrete Appl. Math. (1995), 141-147.
