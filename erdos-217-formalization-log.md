# Erdős Problem 217 - Formalization Log

## Problem Statement

For which $n$ are there $n$ points in $\mathbb{R}^2$, no three on a line and no four on a circle, which determine $n-1$ distinct distances and so that (in some ordering of the distances) the $i$th distance occurs $i$ times?

## Status

**OPEN**

## Key Results

1. **Example with $n=4$**: An isosceles triangle with a point in the center
2. **$n=5$ construction**: Pomerance constructed an example with 5 points
3. **Lower bound**: Palásti proved such sets exist for all $n \leq 8$

## Conjecture

Erdős believed this is impossible for all sufficiently large $n$. This would follow from $h(n) \geq n$ for sufficiently large $n$, where $h(n)$ is as in Problem 98.

## Formalization Details

### Main Components

1. **`NoFourConcyclic`**: Predicate ensuring no four points in the set are concyclic (lie on a common circle)

2. **`Distances`**: Computes the set of all pairwise distances in a finite point set

3. **`HasDistanceCounts`**: Checks if a set of $n$ points has exactly $n-1$ distinct distances where the $i$-th distance occurs exactly $i$ times (considering ordered pairs, so $2i$ pairs total)

4. **`erdos_217`**: The set of all values $n$ for which such a configuration exists

### Theorems Formalized

- `erdos_217.lb`: Such sets exist for all $n \leq 8$ (Palásti)
- `erdos_217.sufficiently_large`: Conjecture that such sets don't exist for sufficiently large $n$ (Erdős)

## Technical Notes

- The `Distances` function is marked as `noncomputable` because it depends on decidable equality for real numbers
- The problem asks "for which $n$", so we define `erdos_217` as a `Set ℕ` rather than a boolean predicate
- Distance counts are doubled (factor of 2) to account for ordered pairs

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/217.lean`
⚠️ Warning about open categorization (expected for this type of problem)
