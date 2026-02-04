# Erdős Problem 169 Formalization Log

## Problem Statement

Let $k\geq 3$ and $f(k)$ be the supremum of $\sum_{n\in A}\frac{1}{n}$ as $A$ ranges over all sets of positive integers which do not contain a $k$-term arithmetic progression. Estimate $f(k)$. Is $\lim_{k	o \infty}\frac{f(k)}{\log W(k)}=\infty$ where $W(k)$ is the van der Waerden number?

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/169.lean`
- **Definition:** `f k` is the supremum of sums $\sum_{n \in A} 1/n$ for $k$-AP free sets $A \subseteq \mathbb{N}^+$.
- **Definition:** `W k` is the van der Waerden number for 2 colors and progression length $k$.
- **Theorem:** `erdos_169` states that the ratio $f(k) / \log W(k)$ tends to infinity as $k 	o \infty$.

## Implementation Notes

- Used `Real.sSup` for the supremum.
- Used `HasSum` to represent the sum of the reciprocal series.
- Borrowed the definition of $W(k)$ from `FormalConjectures/ErdosProblems/138.lean`.
- Used `Filter.Tendsto ... atTop atTop` for the limit to infinity.

## Build Status

- Built with `lake build FormalConjectures/ErdosProblems/169.lean`.
