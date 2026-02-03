# Erdos Problem 127 Formalization Log

## Problem Description

Erdos Problem 127 asks if $f(m)$, the excess of the max bipartite cut over the Edwards bound for graphs with $m$ edges, tends to infinity for some sequence of $m$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/127.lean`
- **Theorem Name:** `Erdos127.erdos_127`
- **Status:** Proved by Alon [Al96].

We defined:
- `MaxBipartiteEdges`
- `EdwardsBound`
- `f(m)` (restricted to graphs on `Fin (2*m)`).

The theorem states the existence of a sequence $m_k \to \infty$ such that $f(m_k) \to \infty$.

## References

- [Ed73] Edwards, C. S., "Some extremal properties of bipartite subgraphs", Canad. J. Math. (1973), 475-485.
- [Al96] Alon, N., "Bipartite subgraphs", Combinatorica (1996), 301-311.

