# AI Formalization - Erdos Problems

## Style

The `README.md` contains style guidance that should be adhered to for lean formalizations. 

## Fetch data

To fetch the overview of the numbered Erdos Problem, retrieve the following URL:

```
https://www.erdosproblems.com/NUMBER
```

## Lean file location

Files should be located in:

```
FormalConjectures/ErdosProblems/NUMBER.lean
```

## Determine unformalized problems

To determine all unformalized problems:

1. Get list of all problem numbers marked as not-yet-formalized from `unformalized-erdos-problems.txt`
2. List all lean files in `FormalizedConjectures/ErdosProblems/`
3. Diff these sets (ensure sorting is in numerical order)

## Build

To build, just build the particular file in question, using its filepath:

```
lake build FormalConjectures/ErdosProblems/NUMBER.lean
```

NOTE: do NOT run `lake clean` while debugging. Stop working on specific problem if lake build continues to fail.

## Documentation

Summarize details of formalizing the particular conjecture in a file:

```
erdos-NUMBER-formalization-log.md
```

## Git

- Commit changes after each individual problem is formalized.
- Do not push unless explicitly instructed by user.
