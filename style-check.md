# Style Guidelines Checklist for Lean Formalizations

This checklist is derived from the [README](./README.md) style guidelines (lines 212-264) and attribute requirements. Use it to verify that a formalized conjecture adheres to the repository's standards.

## Checklist

### File Structure & Organization

- [ ] **1. One problem per file** (with flexibility for variants/special cases in same file)
- [ ] **2. Correct directory structure** - File placed in appropriate source directory (e.g., `FormalConjectures/ErdosProblems/` for Erdős problems)
- [ ] **3. Copyright header present** - Exact format with 2026 date:
  ```lean
  /-
  Copyright 2026 The Formal Conjectures Authors.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
  -/
  ```

### Problem Statement Format

- [ ] **4. Uses `theorem` or `lemma` keyword** - Not `def` or other keywords
- [ ] **5. Question format** - If problem asks a question ("Does P hold?", "Are there...", "Is it true that..."), use:
  ```lean
  /-- English version: "Does P hold?" -/
  theorem myConjecture : answer(sorry) ↔ P := by
    sorry
  ```
  For solved questions: `answer(True)` or `answer(False)` instead of `answer(sorry)`

- [ ] **6. Statement format** - If not a question ("P holds"), use:
  ```lean
  /-- English version: "P holds" -/
  theorem myConjecture : P := by
    sorry
  ```
  For negatively solved statements: use `¬ P`

### Attributes & Tags

- [ ] **7. `@[category]` attribute present** - Must specify one of:
  - `research open` - Open research problem with no accepted solution
  - `research solved` - Problem with established solution (formal proof here, elsewhere, or informal)
  - `graduate`, `undergraduate`, `high school` - Only if directly related to research problem
  - `API statement` - Constructs basic theory around new definition
  - `test` - Serves as unit test for definitions/statements

- [ ] **8. `@[AMS]` attribute present** - At least one AMS subject code (00-99, from [AMS MSC2020](https://mathscinet.ams.org/mathscinet/msc/pdfs/classifications2020.pdf))
- [ ] **9. Both attributes on same theorem** - Combined format: `@[category research open, AMS 11]`

### Documentation & References

- [ ] **10. File docstring present** - Module-level documentation:
  ```lean
  /-!
  # Problem Title

  Brief description.

  STATUS (OPEN/SOLVED/etc.)

  *Reference:* [source](URL)
  -/
  ```

- [ ] **11. Reference URL included** - Link to original source (paper, website, book, arxiv, etc.)
- [ ] **12. Problem description** - Explain what mathematical question is being formalized
- [ ] **13. Theorem docstring** - `/-- ... -/` comment above theorem with explanation

### Definitions & API

- [ ] **14. Bespoke definitions allowed** - Custom definitions are permitted if they clarify the problem statement
- [ ] **15. Basic API provided** - For custom definitions, include basic lemmas/theorems to test that they behave as expected

### Code Quality

- [ ] **16. Code builds** - `lake build FormalConjectures/Path/To/File.lean` succeeds without errors
- [ ] **17. Import structure** - Appropriate imports (e.g., single import of `FormalConjectures.Util.ProblemImports` for standard setup)
- [ ] **18. Namespace usage** - Problem wrapped in appropriate namespace (e.g., `namespace Erdos1149 ... end Erdos1149`)

### Answer Elaborator Usage

- [ ] **19. `answer(sorry)` for unknowns** - When the answer is unknown or problem is open
- [ ] **20. `answer(True/False)` for solved boolean questions** - When a yes/no question has been answered
- [ ] **21. Correct answer elaborator position** - Should appear where the unknown value is needed in the statement

## Notes on Answer Elaborator

From README: Providing a term inside `answer( )` together with a proof does NOT necessarily mean the problem is solved. Trivial or non-meaningful answers can satisfy the formal statement without solving the mathematical problem.

Example of trivial answer:
```lean
-- Question: "Which natural numbers satisfy P?"
theorem myOpenProblem : {n : ℕ | P n} = answer(sorry) := by sorry
-- Trivial answer: answer({n : ℕ | P n}) -- formally correct but not meaningful!
```

The question of whether an answer is mathematically meaningful is outside the scope of formal verification.

## Common Patterns

### For Erdős Problems
- File: `FormalConjectures/ErdosProblems/NNNN.lean`
- Namespace: `ErdosNNNN`
- Import: `import FormalConjectures.Util.ProblemImports`
- Reference: `[erdosproblems.com/NNNN](https://www.erdosproblems.com/NNNN)`
- AMS code: Typically 05 (combinatorics), 11 (number theory), 03 (set theory), etc.

### For Questions vs Statements
- **Question form**: "Is X equal to Y?" → `answer(sorry) ↔ (X = Y)`
- **Statement form**: "X equals Y" → `X = Y`
- **Existence question**: "Does X exist?" → `answer(sorry) ↔ ∃ x, P x`
- **Existence statement**: "X exists" → `∃ x, P x`
