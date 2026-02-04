# Erdős Problem 180 Formalization Log

## Date: February 4, 2026

## Objective
Formalize Erdős Problem 180 in `FormalConjectures/ErdosProblems/180.lean`.

## Process
1.  **Identification:**
    - Read the problem statement from `html-erdos-180.html`.
    - Problem asks if for every finite family $\mathcal{F}$, there exists $G \in \mathcal{F}$ such that $\mathrm{ex}(n; G) = O(\mathrm{ex}(n; \mathcal{F}))$.
    - Noted the counterexample by Zach Hunter (star and matching) which shows the general statement is false.

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/180.lean`.
    - Defined `TuranNumber` using `SimpleGraph.Embedding` (`↪g`).
    - Defined `TuranNumberFamily` for a collection of graphs.
    - Stated the conjecture as `erdos_180` using `answer(False)` since the general statement is false.
    - Added documentation explaining the counterexample.

3.  **Verification:**
    - Ran `lake build FormalConjectures/ErdosProblems/180.lean` and it passed.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/180.lean` (Created)
- `erdos-180-formalization-log.md` (Created)
