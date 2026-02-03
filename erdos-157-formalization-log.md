# Erdős Problem 157 Formalization Log

The problem asks whether there exists an infinite Sidon set which is an asymptotic additive basis of order 3.

## Problem Statement

Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

## Formalization Details

- **Sidon set**: Formalized using `IsSidon` from `FormalConjecturesForMathlib.Combinatorics.Basic`.
- **Asymptotic additive basis of order 3**: Formalized using `IsAsymptoticAddBasisOfOrder 3` from `FormalConjecturesForMathlib.Combinatorics.Additive.Basis`.
- **Question format**: Uses `answer(True)` since the problem has been solved in the affirmative.

## Status

Solved in the affirmative by Pilatte [Pi23].

## References

- [erdosproblems.com/157](https://www.erdosproblems.com/157)
- [ESS94] P. Erdős, A. Sárközy, and V. T. Sós, "On sumsets of Sidon sets. I", J. Number Theory 47 (1994), 329–347.
- [Pi23] C. Pilatte, "Sidon sets that are asymptotic bases", arXiv:2310.12876, 2023.
