# Erdős Problem 18 Formalization Session Log

## Date: January 30, 2026

## Objective
Formalize Erdős Problem 18 in `FormalConjectures/ErdosProblems/18.lean`.

## Process
1.  **Identification:**
    - Used content from `erdos-problems-html/18.html`.
    - Statement: "Are there infinitely many practical $m$ such that $h(m) < (\log\log m)^{O(1)}$? Is it true that $h(n!) < n^{o(1)}$? Or perhaps even $h(n!) < (\log n)^{O(1)}$?"
    - Status: "open".

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/18.lean`.
    - Defined `IsPractical m` and `h m`.
    - Defined `erdos_18` as the first question (infinite practical numbers with small $h$).
    - Added variants for the factorial conjectures: `factorial_small` ($n^{o(1)}$) and `factorial_log` ($(\log n)^{O(1)}$).
    - Used `answer(sorry)` as it is open.

3.  **Verification:**
    - Successfully built `FormalConjectures/ErdosProblems/18.lean`.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/18.lean` (Created)
