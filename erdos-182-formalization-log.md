# Erdős Problem 182 Formalization Log

## Date: February 4, 2026

## Objective
Formalize Erdős Problem 182 in `FormalConjectures/ErdosProblems/182.lean`.

## Process
1.  **Identification:**
    - Read the problem statement from `html-erdos-182.html`.
    - Problem asks for the maximum number of edges in a graph without a $k$-regular subgraph.
    - Specifically asks if it is $\ll n^{1+o(1)}$.
    - Noted it was solved by Janzer and Sudakov [JaSu23] who showed it is $O(n \log \log n)$.

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/182.lean`.
    - Defined `ContainsKRegularSubgraph` using `SimpleGraph.IsRegularOfDegree`.
    - Defined `MaxEdgesNoKRegular` as the Turán-type extremal number.
    - Stated the primary conjecture `erdos_182` as `answer(True)` using little-o notation.
    - Added `erdos_182_precise` with the $O(n \log \log n)$ bound.

3.  **Verification:**
    - Ran `lake build FormalConjectures/ErdosProblems/182.lean` and it passed after fixing imports and regularity predicate.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/182.lean` (Created)
- `erdos-182-formalization-log.md` (Created)
