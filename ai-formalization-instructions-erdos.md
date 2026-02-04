# AI Formalization - Erdos Problems

## Fetch data

To fetch the overview of the numbered Erdos Problem, retrieve the following URL:

```
https://www.erdosproblems.com/NUMBER
```

## Canonical dataset

The file at `erdos-problems-data.yaml` is the canonical source of erdos problems and their current status. Review this file to determine which ones are currently marked as formalized versus not.

## Lean file location

Files should be located in:

```
FormalConjectures/ErdosProblems/NUMBER.lean
```

## Determine unformalized problems

To determine all unformalized problems:

1. Get list of all problems marked as not-yet-formalized from `erdos-problems-data.yaml`
2. List all lean files in `FormalizedConjectures/ErdosProblems/`
3. Diff these sets

## Build

To build, just build the particular file in question:

```
lake build FormalConjectures/ErdosProblems/NUMBER.lean
```

## Documentation

Summarize details of formalizing the particular conjecture in a file:

```
erdos-NUMBER-formalization-log.md
```

## Git

- Commit changes after every file formalized.
- Do not push unless explicitly instructed by user.
