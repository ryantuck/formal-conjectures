# Erdős Problem 162 Formalization Log

## Conjecture

Let `α > 0` and `n ≥ 1`. Let `F(n, α)` be the largest `k` such that there exists some 2-colouring of the edges of `Kₙ` in which any induced subgraph `H` on at least `k` vertices contains more than `α * (vchoose (Fintype.card H) 2)` edges of each colour.

For every fixed `0 ≤ α ≤ 1/2`, as `n → ∞`, `F(n, α) ~ c * log n` for some constant `c`.

## Formalization

I defined `Erdmulticolor n k α c` to be the property that a 2-edge-colouring `c` of `Kₙ` has the desired property for a given `k` and `α`.

Then, `F(n, α)` is defined as the supremum over all `k` for which such a coloring exists.

The conjecture `erdos_162` states that for a given `α` in the specified range, there exists a constant `c` such that `F(n, α)` is asymptotically equivalent to `c * log n`.

## Status

The conjecture is formalized but not proven. The theorem `erdos_162` has a `sorry` placeholder.
