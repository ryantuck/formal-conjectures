import          Mathlib.NumberTheory.Primes

/-
Let $A=\{n_1<n_2<\cdots\}$ be an infinite sequence of integers,
and let $\phi_A(k)$ count the number of $1\leq m\leq n_k$
such that the fraction $\frac{m}{n_k}$ does not have denominator $n_j$ for $j<k$
when written in lowest form; equivalently,
\[\frac{n_k}{(m,n_k)}
eq n_j\]for all $1\leq j<k$.
-/

-- Is there a sequence $A$ such that
-- \[\lim_{N	o \infty}\frac{1}{N}\sum_{k\leq N}\frac{\phi_A(k)}{n_k}=0?\]

-- This was solved by Haight [Ha] who proved that such a sequence does exist
-- (contrary to Erdős' expectations).

-- We formalize the statement of the conjecture.

def phi_A (A : ℕ → ℕ) (k : ℕ) : ℕ :=
  Fintype.card
    (Finset.filter
      (fun m => ∀ j < k, n_k / Nat.gcd m n_k ≠ n_j)
      (Finset.range (n_k + 1)))

theorem erdos_1000
  (A : ℕ → ℕ)
  (hA : StrictMono A) :
  ∃ A, Tendsto (fun N => (∑ k ∈ Finset.range N, phi_A A k / A k) / N) atTop (𝓝 0) := by
  sorry
