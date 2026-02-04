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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 226

*Reference:* [erdosproblems.com/226](https://www.erdosproblems.com/226)
-/

open Complex

namespace Erdos226

/--
Is there an entire non-linear function $f$ such that, for all $x\in\mathbb{R}$,
$x$ is rational if and only if $f(x)$ is?

Solved by Barth and Schneider [BaSc70], who proved that if $A,B\subset\mathbb{R}$
are countable dense sets then there exists a transcendental entire function $f$
such that $f(z)\in B$ if and only if $z\in A$.

[BaSc70] Barth, K. F. and Schneider, W. J., _Entire functions mapping countable
  dense subsets of the reals onto each other monotonically_.
  J. London Math. Soc. (1970), 620-626.
-/
@[category research solved, AMS 30]
theorem erdos_226 : ∃ f : ℂ → ℂ,
    Differentiable ℂ f ∧
    ¬ (∃ a b : ℂ, f = fun z => a * z + b) ∧
    ∀ x : ℝ, (∃ q : ℚ, (x : ℝ) = q) ↔ (∃ q : ℚ, f x = q) := by
  sorry

end Erdos226
