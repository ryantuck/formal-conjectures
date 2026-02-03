# Erdos Problem 136 Formalization Log

## Problem Description

Erdos Problem 136 asks for the minimal number of colors $f(n)$ to color edges of $K_n$ such that every $K_4$ has at least 5 colors.
Conjecture: $f(n) \sim \frac{5}{6}n$.

## Formalization Details

- **File Location:** `FormalConjectures/ErdosProblems/136.lean`
- **Theorem Name:** `Erdos136.erdos_136`
- **Status:** Solved (Bennett, Cushman, Dudek, and Pralat).

We defined:
- `EdgeColoring`
- `EveryK4Has5Colors'`
- `f(n)` (noncomputable)

The theorem states the limit is $5/6$.

## References

- [BCDP22] Bennett, P., Cushman, C., Dudek, A., and Pralat, P., "A note on edge colorings of complete graphs with rainbow cliques", arXiv:2209.07921 (2022).
- [JoMu22] Joos, F. and Mubayi, D., "Edge colorings of complete graphs with rainbow cliques", arXiv:2209.07921 (2022).
