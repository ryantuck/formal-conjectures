# Erdős Problem 21 Formalization Session Log

## Date: January 30, 2026

## Objective
Formalize Erdős Problem 21 in `FormalConjectures/ErdosProblems/21.lean`.

## Process
1.  **Identification:**
    - Used content from `erdos-problems-html/21.html`.
    - Statement: "Let $f(n)$ be minimal such that there is an intersecting family $\mathcal{F}$ of sets of size $n$ ... such that any set $S$ with $|S| \le n-1$ is disjoint from at least one $A \in \mathcal{F}$. Is it true that $f(n) \ll n$?"
    - Status: "proved" (solved by Kahn [Ka94]).

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/21.lean`.
    - Defined `IsValidFamily n F` for the condition.
    - Defined `f n` as the infimum of cardinalities of valid families.
    - Defined `erdos_21` as the upper bound $f(n) \le Cn$.
    - Cited Kahn [Ka94].

3.  **Verification:**
    - Successfully built `FormalConjectures/ErdosProblems/21.lean`.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/21.lean` (Created)
