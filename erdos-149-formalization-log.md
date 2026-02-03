# Erdos Problem 149 Formalization Log

## Problem Description

Erdos Problem 149 asks if the chromatic number of the square of the line graph of $G$ is at most $\frac{5}{4}\Delta(G)^2$.
Equivalently, can $G$ be covered by at most $\frac{5}{4}\Delta^2$ induced matchings?

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/149.lean`
- **Theorem Name:** `Erdos149.erdos_149`
- **Status:** Open.

We defined:
- `Square`
- `LineGraph`
- `MaxDegree`

The theorem states the bound.

## References

- [Er88c] Erdős, P., "Problems and results in combinatorial analysis and graph theory", Discrete Math. (1988), 81-92.
