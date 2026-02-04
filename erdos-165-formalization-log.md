# Erdős Problem 165 Formalization Log

## Problem Statement

Give an asymptotic formula for $R(3,k)$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/165.lean`
- **Definition:** `erdos_165_Ramsey k` is defined as the off-diagonal Ramsey number $R(3,k)$, the smallest $n$ such that every graph on $n$ vertices contains a $K_3$ or an independent set of size $k$.
- **Conjecture:** Stated that $R(3,k) \sim \frac{1}{2} \frac{k^2}{\log k}$ as $k 	o \infty$. This follows from recent conjectures in [CJMS25] and [HHKP25], based on improvements to the lower bound constant $c$ towards $1/2$ (the upper bound of $(1+o(1)) k^2/\log k$ was proved by Shearer [Sh83]).

## Implementation Notes

- Used `SimpleGraph.CliqueFree 3` to express the absence of triangles.
- Used `α(G)` (notation for `SimpleGraph.indepNum G`) to express the independence number.
- Used `~[atTop]` for asymptotic equivalence.
- Cited Kim [Ki95], Shearer [Sh83], Campos et al. [CJMS25], and Hefty et al. [HHKP25].

## Build Status

- Built with `lake build FormalConjectures/ErdosProblems/165.lean`.
