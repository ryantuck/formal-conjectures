# Erdős Problem 206 Formalization Log

## Problem Statement

Let $x > 0$ be a real number. For any $n \geq 1$ let $R_n(x) = \sum_{i=1}^n \frac{1}{m_i} < x$ be the maximal sum of $n$ distinct unit fractions which is $< x$. Is it true that, for almost all $x$, for sufficiently large $n$, we have $R_{n+1}(x) = R_n(x) + \frac{1}{m}$, where $m$ is minimal such that $m$ does not appear in $R_n(x)$ and the right-hand side is $< x$? (That is, are the best underapproximations eventually always constructed in a 'greedy' fashion?)

## Discovery and Analysis

- The problem asks if the sequence of best underapproximations of $x$ by $n$ unit fractions is eventually greedy.
- $R_n(x)$ is the maximum possible sum.
- The greedy property means $R_{n+1}(x)$ is obtained by adding the largest possible unit fraction to the set that gave $R_n(x)$.
- Curtiss (1922) and Erdős (1950) showed this holds for $x=1$ and $x=1/m$.
- Kovač (2024) proved that this property is false for almost all $x$ (it holds only on a set of measure zero).

## Formalization Plan

- Define $R(n, x)$ as the `sSup` of sums of $n$ distinct unit fractions less than $x$.
- Define `IsBestUnderapproximation` for a set of unit fractions whose sum is $R(n, x)$.
- State the greedy property: $R_{n+1}(x)$ corresponds to adding a minimal $m$ (maximal fraction) to the set for $R_n(x)$.
- State the main theorem with `answer(False)` and a variant for the measure zero result.

## Lean Implementation Details

- Used `sSup` over `Finset ℕ` of size `n` with sum `< x`.
- Used `∀ᵐ x off (Set.Ioi 0)` for almost all $x > 0$.
- Used `MeasureTheory.volume` for the quantified result.

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/206.lean`.
