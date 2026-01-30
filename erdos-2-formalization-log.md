# Erdős Problem 2 Formalization Session Log

## Date: January 30, 2026

## Objective
Expand and improve the formalization of Erdős Problem 2 (The Minimum Modulus Problem) in `FormalConjectures/ErdosProblems/2.lean`, adhering to project style guidelines and incorporating known variants and recent results.

## Work Log

### 1. Initial Assessment
- **Reviewed Style Guidelines:** Checked `README.md` for `answer(sorry)` syntax, category attributes, and referencing standards.
- **Analyzed Current State:**
  - `FormalConjectures/ErdosProblems/2.lean` contained the basic negation of the minimum modulus problem (Hough's result).
  - `FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean` provided the necessary `StrictCoveringSystem` structure.
  - `erdos-problems-data.yaml` listed metadata, indicating the problem status as "disproved".
- **Comparison:** Reviewed `1.lean` to establish a baseline for the expected level of detail and inclusion of variants.

### 2. Research and Variant Identification
- **Term Search:** Searched the codebase for "covering system", "odd moduli", and "Selfridge" to find related unformalized problems.
- **External Verification:**
  - Investigated the "Odd Covering Problem" (Erdős-Selfridge conjecture).
  - Researched bounds on the minimum modulus.
    - **Hough (2015):** Established the first bound ($10^{16}$).
    - **Balister, Bollobás, Morris, Sahasrabudhe, Tiba (2022):** Improved the bound significantly to $616,000$.
  - Investigated the "Square-free Odd Moduli" variant.
    - **Hough & Nielsen (2019):** Proved that any covering system with distinct moduli $>1$ implies divisibility by 2 or 3, effectively resolving the square-free odd case.

### 3. Implementation
Updated `FormalConjectures/ErdosProblems/2.lean` to include the following variants:

#### A. Explicit Bounds
- **Hough's Bound:** Added `erdos_2.variants.bound` stating that the minimum modulus is $\le 10^{16}$.
- **Strong Bound:** Added `erdos_2.variants.bound_strong` referencing [BB+22], improving the bound to $616,000$.

#### B. Odd Moduli Variants
- **Erdős-Selfridge Conjecture:** Added `erdos_2.variants.odd` asking if a covering system exists with distinct odd moduli all $>1$. Marked as `@[category research open]`.
- **Square-free Odd Moduli:** Added `erdos_2.variants.odd_squarefree` referencing [HoNi19], noting the negative resolution.

#### C. Citations
- Added full bibliographic references for:
  - [BB+22] Balister et al. (Geometry & Topology, 2022)
  - [HoNi19] Hough & Nielsen (Duke Mathematical Journal, 2019)

### 4. Metadata Updates
- Modified `erdos-problems-data.yaml`:
  - Updated the `formalized.last_update` field for Problem 2 to `2026-01-30`.

### 5. Verification
- **Compilation:** Executed `lake build FormalConjectures/ErdosProblems/2.lean`.
- **Result:** Build successful with no errors.

## Summary of Files Modified
- `FormalConjectures/ErdosProblems/2.lean` (Major expansion)
- `erdos-problems-data.yaml` (Metadata update)
