# Erdos Problem 161 - Formalization Log

## Problem Statement

Let $\alpha \in [0, 1/2)$ and $n, t \geq 1$. Let $F^{(t)}(n,\alpha)$ be the smallest $m$ such that we can 2-colour the edges of the complete $t$-uniform hypergraph on $n$ vertices such that if $X \subseteq [n]$ with $|X| \geq m$, then there are at least $\alpha \binom{|X|}{t}$ many $t$-subsets of $X$ of each colour.

For fixed $n, t$, as we change $\alpha$ from $0$ to $1/2$, does $F^{(t)}(n,\alpha)$ increase continuously or are there jumps? Only one jump?

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/161.lean`
- **Definition:** `erdos_161.F` defines the smallest $m$ as an `sInf`.
- **Theorems:**
    - `erdos_161.one_jump`: Conjecture that the growth rate is the same for all $\alpha \in (0, 1/2)$.
    - `erdos_161.jump_at_zero`: Conjecture that there is a jump in growth rate at $\alpha=0$.

## Implementation Notes

- Used `Finset.powersetCard` to represent the $t$-subsets of vertices.
- Represented the 2-coloring as a function `f : powersetCard t (univ : Finset (Fin n)) → Fin 2`.
- Used `Filter.atTop` and `Asymptotics.isTheta` to express growth rate equivalence.
- The jump at $\alpha=0$ is formalized by stating that $F^{(t)}(n, \alpha)$ and $F^{(t)}(n, 0)$ do not have the same order of growth for any $\alpha > 0$.

## Build Status

- Successfully built with `lake build FormalConjectures/ErdosProblems/161.lean`.

## Metadata Update

- Updated `erdos-problems-data.yaml` to mark problem 161 as formalized.
