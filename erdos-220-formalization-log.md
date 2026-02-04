# Erdős Problem 220 - Formalization Log

## Problem Statement

Is it true that $\sum_{1 \le k < \phi(n)} (a_{k+1} - a_k)^2 \ll \frac{n^2}{\phi(n)}$, where $a_1 < a_2 < \dots < a_{\phi(n)}$ are the integers $1 \le m < n$ with $(m, n) = 1$?

## Status

**SOLVED** (Yes)

## Key Results

- **Montgomery and Vaughan (1986)** proved the more general result: for any $\gamma \geq 1$,
  $$\sum_{1 \le k < \phi(n)} (a_{k+1} - a_k)^\gamma \ll \frac{n^\gamma}{\phi(n)^{\gamma-1}}$$

## Formalization Details

### Main Components

1. **`CoprimeResidues`**: Computes the sorted list of integers $1 \le m < n$ that are coprime to $n$

2. **`gapSum`**: Computes the sum of $\gamma$-powers of consecutive gaps in the coprime residues

3. **Main theorem `erdos_220`**: The special case with $\gamma = 2$

4. **`erdos_220.variants.general`**: The general result of Montgomery and Vaughan for any $\gamma \geq 1$

## Technical Notes

- `CoprimeResidues` and `gapSum` are marked as `noncomputable` because they depend on operations that are not computationally effective
- Uses `List.mergeSort` to sort the coprime residues
- Gaps are computed by zipping the list with its tail (`L.zip (L.drop 1)`)

## References

- [MoVa86] Montgomery, H. L. and Vaughan, R. C., _On the distribution of reduced residues_. Annals of Math. (1986), 311-333.

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/220.lean`
