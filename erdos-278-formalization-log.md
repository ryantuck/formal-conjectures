# Erdős Problem 278 Formalization Log

## Problem Statement
Given a finite set $A=\{n_1<\cdots<n_r\}$ of positive integers, determine the maximum density of integers that can be covered by selecting suitable congruences $a_i\pmod{n_i}$.

Is the minimum density achieved when all $a_i$ are equal?

## Status
**SOLVED** - Simpson (1986) answered affirmatively.

## Formalization Details

### Main Definitions
- `covering_density A a`: The density of integers covered by congruences
- `simpson_density A`: The minimum density formula

### Key Theorems
1. `erdos_278.simpson`: The minimum density is achieved when all $a_i$ are equal
2. `erdos_278.minimum_equal`: Existence of the minimum configuration

### Category
- `@[category research solved, AMS 11]` - Number theory

## Build Status
✓ Successfully builds with `lake build FormalConjectures/ErdosProblems/278.lean`

## References
- Erdős and Graham (1980)
- Simpson (1986)
- [erdosproblems.com/278](https://www.erdosproblems.com/278)
