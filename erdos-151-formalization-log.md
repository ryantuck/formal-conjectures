# Erdos Problem 151 Formalization Log

## Problem Description

Erdos Problem 151 asks if the clique transversal number $\tau(G)$ satisfies $\tau(G) \le n - H(n)$, where $H(n)$ is the minimum independence number of a triangle-free graph on $n$ vertices.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/151.lean`
- **Theorem Name:** `Erdos151.erdos_151`
- **Status:** Open.

We defined:
- `IsMaximalClique`
- `IsCliqueTransversal`
- `tau`
- `IsIndependentSet`
- `alpha`
- `H(n)`

The theorem states the conjecture.

## References

- [Er88] Erdős, P., "Problems and results in combinatorial analysis and graph theory", Discrete Math. (1988), 81-92.
- [EGT92] Erdős, P., Gallai, T., and Tuza, Z., "Covering the cliques of a graph with vertices", Discrete Math. (1992), 71-78.

