# Erdős Problem 166 Formalization Log

## Problem Statement

Prove that $R(4,k) \gg \frac{k^3}{(\log k)^{O(1)}}$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/166.lean`
- **Definition:** `erdos_166_Ramsey k` is the off-diagonal Ramsey number $R(4,k)$.
- **Theorem:** Stated the existence of $C > 0$ such that $R(4,k) \gg k^3 / (\log k)^C$. This matches the "$\gg k^3 / (\log k)^{O(1)}$" formulation from the problem statement.
- **Status:** Proved by Mattheus and Verstraete [MaVe23] ($C=4$).

## Implementation Notes

- Used `SimpleGraph.CliqueFree 4` and `α(G)` (independence number).
- Used `Asymptotics.isBigO` (notation `=O[atTop]`) to represent $\gg$ as the reverse of $\ll$ (i.e., $f \gg g$ means $g = O(f)$).
- Cited Mattheus and Verstraete [MaVe23].

## Build Status

- Built with `lake build FormalConjectures/ErdosProblems/166.lean`.
