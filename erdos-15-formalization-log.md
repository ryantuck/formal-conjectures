# Erdős Problem 15 Formalization Session Log

## Date: January 30, 2026

## Objective
Formalize Erdős Problem 15 in `FormalConjectures/ErdosProblems/15.lean`.

## Process
1.  **Identification:**
    - Used content from `erdos-problems-html/15.html` to confirm the problem statement.
    - Statement: "Is it true that $\sum_{n=1}^\infty (-1)^n \frac{n}{p_n}$ converges, where $p_n$ is the sequence of primes?"
    - Status: "open".

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/15.lean`.
    - Defined `erdos_15` as the convergence of the alternating series of $n/p_n$.
    - Added variants for related conjectures mentioned in the source:
        - $\sum (-1)^n / (n(p_{n+1}-p_n))$ (open).
        - $\sum (-1)^n / (p_{n+1}-p_n)$ (disproved/solved negatively due to bounded gaps).
    - Cited Tao [Ta23] and Zhang [Zh14].

3.  **Metadata Update:**
    - Updated `erdos-problems-data.yaml`:
        - Changed `formalized.state` to `yes`.
        - Updated `formalized.last_update` to `2026-01-30`.

4.  **Verification:**
    - Successfully built `FormalConjectures/ErdosProblems/15.lean`.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/15.lean` (Created)
- `erdos-problems-data.yaml` (Updated)
