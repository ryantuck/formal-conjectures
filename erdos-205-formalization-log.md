# Erdős Problem 205 Formalization Log

## Problem Statement

Is it true that all sufficiently large $n$ can be written as $2^k+m$ for some $k \geq 0$, where $\Omega(m) < \log \log m$? (Here $\Omega(m)$ is the number of prime divisors of $m$ counted with multiplicity.) What about $< \epsilon \log \log m$? Or some more slowly growing function?

## Discovery and Analysis

- The problem asks if $n - 2^k$ can always have few prime factors for some $k$.
- Romanoff (1934) showed that $2^k + p$ has positive density.
- Erdős used covering systems to show that some odd integers are not representable as $2^k + p$.
- Recent work by Barreto and Leeham (using ChatGPT and Aristotle) disproved the conjecture.
- Tao and Alexeev quantified this: there are infinitely many $n$ such that for all $k$ with $2^k < n$, $n - 2^k$ has at least $\gg (\frac{\log n}{\log \log n})^{1/2}$ prime factors.
- Since $(\frac{\log n}{\log \log n})^{1/2}$ grows much faster than $\log \log n$, the answer to Erdős's question is NO.

## Formalization Plan

- Define `Omega m` using `m.factors.length`.
- State the main conjecture as a bi-implication with `answer(False)`.
- State the Tao-Alexeev result as a variant.
- Use `∀ᶠ (n : ℕ) in atTop` for "all sufficiently large $n$".
- Use `∃ n ≥ N` for "infinitely many $n$".

## Lean Implementation Details

- `m.factors` in Mathlib gives the list of prime factors with multiplicity.
- `Real.log` and `Real.sqrt` for the bounds.
- `atTop` filter for asymptotic statements.

## Verification Results

- Verified with `lake build FormalConjectures/ErdosProblems/205.lean`.
