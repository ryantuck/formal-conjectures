# Erdős Problem 221 - Formalization Log

## Problem Statement

Is there a set $A \subseteq \mathbb{N}$ such that $|A \cap \{1, \dots, N\}| \ll N/\log N$ and such that every large integer can be written as $2^k + a$ for some $k \geq 0$ and $a \in A$?

## Status

**SOLVED**

## Key Results

- **Ruzsa (2001)** constructed such a set $A$ with $|A \cap \{1, \dots, N\}| \sim N/\log_2 N$

## Formalization Details

### Main Components

1. **`IsAdditiveComplementOfPowersOfTwo`**: A set $A$ is an additive complement of powers of two if every sufficiently large integer can be written as $2^k + a$ for some $k \geq 0$ and $a \in A$

2. **Main theorem `erdos_221`**: Existence of a set $A$ that is an additive complement of powers of two with density $O(N/\log N)$

3. **`erdos_221.ruzsa_best`**: Ruzsa's construction achieving density $\sim N/\log_2 N$

## References

- [Ru01] Ruzsa, I. Z., _On a problem of Erdős concerning the proximity of consecutive elements of an additive basis_. Acta Arith. (2001), 329-336.

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/221.lean`
