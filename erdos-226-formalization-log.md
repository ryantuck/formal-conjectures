# Erdős Problem 226 - Formalization Log

## Problem Statement

Is there an entire non-linear function $f$ such that, for all $x \in \mathbb{R}$, $x$ is rational if and only if $f(x)$ is?

## Status

**SOLVED** (Yes, such functions exist)

## Formalization Details

### Main Components

The problem asks for the existence of an entire function $f : \mathbb{C} \to \mathbb{C}$ such that:
1. $f$ is differentiable everywhere (entire function)
2. $f$ is not linear (i.e., not of the form $f(z) = az + b$)
3. For all real $x$, $x$ is rational if and only if $f(x)$ is rational

### Theorem

**`erdos_226`**: States the existence of such a function, with the answer being `True`

## Technical Notes

- The function is defined on the complex plane but the rationality condition only applies to real inputs
- The non-linearity condition explicitly excludes functions of the form $f(z) = az + b$
- Uses Lean's `Differentiable ℂ f` to express that $f$ is an entire function

## Build Status

✅ Successfully built with `lake build FormalConjectures/ErdosProblems/226.lean`
