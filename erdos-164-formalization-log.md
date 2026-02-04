# Erdős Problem 164 Formalization Log

## Conjecture

A set $A \subset \mathbb{N}$ is primitive if no member of $A$ divides another. The conjecture states that the sum
\[ \sum_{n \in A} \frac{1}{n \log n} \]
is maximized over all primitive sets (where $n > 1$) when $A$ is the set of primes.

## Formalization

I defined `IsPrimitive` as:
```lean
def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ {m n : ℕ}, m ∈ A → n ∈ A → m ∣ n → m = n
```

The theorem `erdos_164` states that for any primitive set $A$ of natural numbers greater than 1, the infinite sum $\sum_{n \in A} \frac{1}{n \log n}$ is less than or equal to the sum for primes.

The sum is expressed using `tsum` (via the notation `∑'`). The condition $n > 1$ ensures that $\log n > 0$, making the terms well-defined and positive.

## Status

The conjecture was proved by Jared Lichtman in 2023. It is formalized here as a `theorem` with a `sorry` placeholder.

The theorem is marked with `category research solved` and `AMS 11`.
