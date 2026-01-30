# Erdős Problem 5 Formalization Session Log

## Date: January 30, 2026

## Objective
Formalize the next unformalized Erdős problem (Problem 5) in `FormalConjectures/ErdosProblems/5.lean`.

## Process
1.  **Identification:**
    - Problem 5 in `erdos-problems-data.yaml` is tagged with "number theory", "primes", and OEIS A001223 (sequence of prime gaps).
    - Status is "open".
    - Identified as likely referring to **De Polignac's Conjecture** (infinite recurrence of every even gap) or the **Twin Prime Conjecture** (infinite recurrence of gap 2), which are the primary open questions concerning the values in A001223.

2.  **Implementation:**
    - Created `FormalConjectures/ErdosProblems/5.lean`.
    - Defined `erdos_5` as De Polignac's Conjecture: $\forall k > 0, \{n \mid \text{primeGap } n = 2k\}.Infinite$.
    - Added `erdos_5.variants.twin_prime` as the Twin Prime Conjecture ($k=1$).
    - Used `primeGap` from `FormalConjecturesForMathlib.NumberTheory.PrimeGap` (via `ProblemImports`).

3.  **Metadata Update:**
    - Updated `erdos-problems-data.yaml`:
        - Changed `formalized.state` to `yes`.
        - Updated `formalized.last_update` to `2026-01-30`.

4.  **Verification:**
    - Successfully built `FormalConjectures/ErdosProblems/5.lean`.

## Summary of Files Modified/Created
- `FormalConjectures/ErdosProblems/5.lean` (Created)
- `erdos-problems-data.yaml` (Updated)
