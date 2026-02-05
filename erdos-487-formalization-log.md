# Erdős Problem 487 - Formalization Log

## Problem Statement

Let A ⊆ ℕ have positive density. Must there exist distinct a,b,c ∈ A such that [a,b] = c
(where [a,b] denotes the least common multiple)?

## Status

PROVED (affirmative answer)

## Key Results

- Davenport and Erdős: A set with positive upper logarithmic density contains an infinite chain
  a₁ < a₂ < ⋯ where each element divides all subsequent ones
- The affirmative answer follows from Problem 447 (Kleitman)

## Formalization Approach

1. **Density measures** (abstract axioms):
   - `upperDensity`: upper density of a set
   - `upperLogDensity`: upper logarithmic density of a set

2. **LCM triple property** (`HasLCMTriple`):
   - Set contains distinct a,b,c ∈ A with lcm(a,b) = c

3. **Davenport-Erdős theorem** (`davenport_erdos_chain`):
   - Positive logarithmic density implies existence of infinite divisibility chain

4. **Main theorem** (`positive_density_has_lcm_triple`):
   - Sets with positive density contain LCM triples

5. **Log density variant** (`positive_log_density_has_lcm_triple`):
   - Alternative formulation using logarithmic density

## Technical Notes

- Used axioms for density definitions due to decidability issues with set membership
- StrictMono used for strictly increasing sequences
- Divisibility relation (∣) used for chain property

## References

- Erdős, 1961, 1965
- Davenport and Erdős
- Problem 447 (Kleitman)
