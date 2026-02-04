# Erdős Problem 181 Formalization Log

## Date: February 4, 2026

## Objective
Formalize Erdős Problem 181 in `FormalConjectures/ErdosProblems/181.lean`.

## Process
1.  **Identification:**
    - Read the problem statement from `html-erdos-181.html`.
    - Problem asks to prove $R(Q_n) \ll 2^n$, where $Q_n$ is the $n$-dimensional hypercube.
    - Noted it's an open conjecture by Burr and Erdős.

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/181.lean`.
    - Defined `HypercubeGraph` as a `SimpleGraph (Fin n → Bool)`.
    - Defined `graphRamsey` for a general finite graph $H$.
    - Stated the conjecture as `erdos_181` asserting the existence of a constant $C > 0$.

3.  **Verification:**
    - Ran `lake build FormalConjectures/ErdosProblems/181.lean` and it passed.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/181.lean` (Created)
- `erdos-181-formalization-log.md` (Created)
