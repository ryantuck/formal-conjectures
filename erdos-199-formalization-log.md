# Erdős Problem 199 Formalization Log

## Problem Statement

If $A\subset \mathbb{R}$ does not contain a 3-term arithmetic progression then must $\mathbb{R}\backslash A$ contain an infinite arithmetic progression?

## Discovery and Analysis

- The problem asks whether the complement of any set $A \subset \mathbb{R}$ without a 3-term AP must contain an infinite AP.
- The answer is NO, as shown by Baumgartner (1975).
- A 3-term AP in $A$ is a set of three distinct points $\{x, y, z\} \subset A$ such that $x+z = 2y$.
- An infinite AP in $A^c$ is a set $\{a + nd : n \in \mathbb{N}\}$ with $d 
e 0$.
- Baumgartner's construction uses a basis for $\mathbb{R}$ over $\mathbb{Q}$ (Hamel basis), which requires the Axiom of Choice.
- In Lean, we can use `Set ℝ`.

## Formalization Plan

- Use `Set ℝ` for $A$.
- Define `HasNoThreeTermAP A` as the property that no three distinct elements of $A$ form an AP.
- Define `HasInfiniteAP S` as the property that $S$ contains a set $\{a + nd : n \in \mathbb{N}\}$ for some $a \in \mathbb{R}$ and $d 
e 0$.
- State the theorem as the negation of the implication: `¬ (∀ A : Set ℝ, HasNoThreeTermAP A → HasInfiniteAP (Aᶜ))`.
- This is equivalent to `∃ A : Set ℝ, HasNoThreeTermAP A ∧ ¬ HasInfiniteAP (Aᶜ)`.

## Lean Implementation Details

- `HasNoThreeTermAP A := ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + z = 2 * y → x = y`. (Since $x+z=2y$ and $x=y$ implies $z=x$, so $x=y=z$).
- `HasInfiniteAP S := ∃ a d : ℝ, d ≠ 0 ∧ ∀ n : ℕ, a + n * d ∈ S`.
- The theorem will be marked as `research solved` (disproved).

## Verification Results

- To be verified with `lake build`.
