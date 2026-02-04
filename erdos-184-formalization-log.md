# Erdős Problem 184 Formalization Log

## Date: February 4, 2026

## Objective
Formalize Erdős Problem 184 in `FormalConjectures/ErdosProblems/184.lean`.

## Process
1.  **Identification:**
    - Read the problem statement from `html-erdos-184.html`.
    - Problem asks to prove that any graph on $n$ vertices can be decomposed into $O(n)$ edge-disjoint cycles and edges.
    - This is the Erdős-Gallai conjecture.

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/184.lean`.
    - Defined `IsCycleSubgraph` as a graph whose non-isolated vertices form a `cycleGraph n` for $n \geq 3$.
    - Defined `IsSingleEdge` as a graph with exactly one edge.
    - Stated the conjecture `erdos_184` as the existence of a decomposition into $O(n)$ such subgraphs.

3.  **Verification:**
    - Ran `lake build FormalConjectures/ErdosProblems/184.lean` and it passed.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/184.lean` (Created)
- `erdos-184-formalization-log.md` (Created)
