# Erdős Problem 19 Formalization Session Log

## Date: January 30, 2026

## Objective
Formalize Erdős Problem 19 in `FormalConjectures/ErdosProblems/19.lean`.

## Process
1.  **Identification:**
    - Used content from `erdos-problems-html/19.html`.
    - Statement: "If $G$ is an edge-disjoint union of $n$ copies of $K_n$ then is $\chi(G)=n$?" (Erdős-Faber-Lovász conjecture).
    - Status: "decidable" (proved for large $n$ by Kang et al. [KKKMO21]).

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/19.lean`.
    - Defined `erdos_19` using `SimpleGraph` and `Set.ncard`.
    - Expressed the edge-disjoint union of cliques explicitly.
    - Used `answer(sorry)` as the full result is not formalized in Mathlib and for small $n$ it's just "decidable".
    - Cited Kang et al. [KKKMO21].

3.  **Verification:**
    - Successfully built `FormalConjectures/ErdosProblems/19.lean`.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/19.lean` (Created)
