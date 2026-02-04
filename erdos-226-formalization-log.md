# Erdős Problem 226 - Formalization Log

## Problem Statement

Is there an entire non-linear function $f$ such that, for all $x\in\mathbb{R}$, $x$ is rational if and only if $f(x)$ is?

## Status

**PROVED** (Yes, such functions exist) - Verified in Lean

## Key Results

- **Barth and Schneider [BaSc70]**: Proved that if $A,B\subset\mathbb{R}$ are countable dense sets, then there exists a transcendental entire function $f$ such that $f(z)\in B$ if and only if $z\in A$
- **Extension [BaSc71]**: Extended to countable dense subsets of $\mathbb{C}$

## More General Result

If $A,B\subseteq \mathbb{R}$ are two countable dense sets, then there exists an entire function such that $f(A)=B$.

## Formalization Details

### Main Theorem

**`erdos_226`**: There exists an entire function $f : \mathbb{C} \to \mathbb{C}$ such that:
1. $f$ is differentiable everywhere (entire function)
2. $f$ is not linear
3. For all real $x$, $x$ is rational if and only if $f(x)$ is rational

## Technical Notes

- An entire function is one that is complex-differentiable everywhere
- The non-linearity condition explicitly rules out $f(z) = az + b$
- The rationality condition only applies when restricting to real inputs

## References

- [BaSc70] Barth, K. F. and Schneider, W. J., _Entire functions mapping countable dense subsets of the reals onto each other monotonically_. J. London Math. Soc. (1970), 620-626.
- [BaSc71] Extension to complex case

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/226.lean`
