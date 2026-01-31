# Erdős Problem 34 Formalization Session Log

## Date: January 30, 2026

## Objective
Formalize Erdős Problem 34 in `FormalConjectures/ErdosProblems/34.lean`.

## Process
1.  **Identification:**
    - Used content from `erdos-problems-html/34.html`.
    - Statement: "For any permutation $\pi \in S_n$, let $S(\pi)$ count the number of distinct consecutive sums. Is it true that $S(\pi) = o(n^2)$?"
    - Status: "disproved" (solved by Konieczny [Ko15]).

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/34.lean`.
    - Defined `distinctConsecutiveSums n π` as the cardinality of the image of sums of consecutive elements.
    - Defined `erdos_34` as the condition that the maximum $S(\pi)$ over all $\pi$ is $o(n^2)$.
    - Used `answer(False)`.

3.  **Verification:**
    - Successfully built `FormalConjectures/ErdosProblems/34.lean`.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/34.lean` (Created)
