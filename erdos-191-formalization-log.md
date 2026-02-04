# Erdős Problem 191 Formalization Log

## Date: February 4, 2026

## Objective
Formalize Erdős Problem 191 in `FormalConjectures/ErdosProblems/191.lean`.

## Process
1.  **Identification:**
    - Read the problem statement from `html-erdos-191.html`.
    - Problem asks if for every $C > 0$, any 2-coloring of edges of $\{2, \dots, n\}$ (for large $n$) contains a monochromatic subset $X$ such that $\sum_{x \in X} 1/\log x \geq C$.
    - Confirmed it's solved by Rödl [Ro03].

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/191.lean`.
    - Defined `Pairs` of a set and `IsMonochromatic` for edge colorings.
    - Stated the theorem `erdos_191` using a subtype for the vertex set $\{2, \dots, n\}$.
    - Marked definitions as `noncomputable`.

3.  **Verification:**
    - Ran `lake build FormalConjectures/ErdosProblems/191.lean` and it passed.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/191.lean` (Created)
- `erdos-191-formalization-log.md` (Created)
