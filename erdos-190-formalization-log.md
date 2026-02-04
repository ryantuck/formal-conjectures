# Erdős Problem 190 Formalization Log

## Date: February 4, 2026

## Objective
Formalize Erdős Problem 190 in `FormalConjectures/ErdosProblems/190.lean`.

## Process
1.  **Identification:**
    - Read the problem statement from `html-erdos-190.html`.
    - Problem asks to estimate $H(k)$, the smallest $N$ such that any coloring of $\{1, \dots, N\}$ has a monochromatic or rainbow $k$-AP.
    - Specifically asks if $H(k)^{1/k}/k 	o \infty$.

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/190.lean`.
    - Defined `IsAP`, `IsMonochromatic`, and `IsRainbow`.
    - Defined `H(k)` using `sInf` over colorings with finite color types.
    - Stated the conjecture `erdos_190` using `Filter.Tendsto` to `atTop`.

3.  **Verification:**
    - Ran `lake build FormalConjectures/ErdosProblems/190.lean` and it passed.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/190.lean` (Created)
- `erdos-190-formalization-log.md` (Created)
