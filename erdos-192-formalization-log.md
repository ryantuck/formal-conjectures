# Erdős Problem 192 Formalization Log

## Problem Statement

Let $A=\{a_1,a_2,\ldots\}\subset \mathbb{R}^d$ be an infinite sequence such that $a_{i+1}-a_i$ is a positive unit vector (i.e. is of the form $(0,0,\ldots,1,0,\ldots,0)$). For which $d$ must $A$ contain a three-term arithmetic progression?

## Discovery and Analysis

- The problem asks for the values of $d$ such that any sequence starting from some point in $\mathbb{R}^d$ and moving by unit vectors at each step must contain three points in an arithmetic progression.
- The additional text states that this is true for $d \le 3$ and false for $d \ge 4$.
- The problem is equivalent to the existence of abelian squares in infinite strings. An abelian square is a word of the form $uv$ where $v$ is a permutation of $u$.
- If $a_n, a_m, a_k$ (with $n < m < k$) form an AP, then $a_m - a_n = a_k - a_m$. Let $v = a_m - a_n$. The coordinates of $v$ count how many times each unit vector was used between $n$ and $m$.
- Since each step is a unit vector, the sum of coordinates of $a_{i+1} - a_i$ is always 1.
- Thus, the sum of coordinates of $a_m - a_n$ is $m-n$, and for $a_k - a_m$ it is $k-m$.
- If $a_m - a_n = a_k - a_m$, then $m-n = k-m$, so the indices $n, m, k$ are also in AP.
- The condition $a_m - a_n = a_k - a_m$ is exactly saying that the multiset of "steps" in $[n, m-1]$ is the same as in $[m, k-1]$. This is the definition of an abelian square in the string of steps.
- Keränen (1992) proved that there exists an infinite string over 4 letters with no abelian squares.
- For $d \le 3$, it is known that every infinite string contains an abelian square.

## Formalization Plan

- Use `Fin d → ℝ` to represent $\mathbb{R}^d$.
- Define the unit vector condition: `∀ n, ∃ i : Fin d, A (n + 1) - A n = Pi.single i 1`.
- Define a 3-term AP in the sequence: `∃ i j k, i < j ∧ j < k ∧ A i + A k = 2 • A j`.
- State the theorem as a bi-implication: the property holds if and only if $d \le 3$.

## Lean Implementation Details

- `Pi.single i 1` represents the unit vector $e_i$.
- `HasThreeTermAP` predicate.
- The conjecture: `∀ (d : ℕ), (∀ (A : ℕ → (Fin d → ℝ)), (∀ n, ∃ i, A (n + 1) - A n = Pi.single i 1) → HasThreeTermAP A) ↔ d ≤ 3`.

## Verification Results

- To be verified with `lake build`.
