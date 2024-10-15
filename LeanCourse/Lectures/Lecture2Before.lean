import LeanCourse.Common
open Real
noncomputable section







/-
# Practical remarks
* To get the latest version of this repository, run `git pull` on the command line.
  See `README` for precise instructions.
* The first assignment due 22.10.2023. Upload it to eCampus.

**Two optional activities**
* There is a weekly Lean hacking session 18 - 20 c.t. in seminar room 0.011.
* There is a Lean seminar Fri 14 - 16 c.t. in N0.003.
  In the next few weeks (starting this Friday) we will explain
  monadic programming and metaprogramming in Lean.
  (Some general programming experience is expected.)
-/

/- # Last Week -/

/- You type code on the left-hand side of the screen,
and Lean automatically compiles the file and
shows output in the *Lean Infoview* on the right.

If you ever close the Infoview, you can toggle it
under the `∀`-button at the top-right of your window. -/

/- Every expression in Lean has a type,
and when applying a function to an argument,
the argument must lie in the domain of the function.  -/
#check 1
#check fun x : ℝ ↦ x^2
#check (fun x : ℝ ↦ x^2) (π + 3)

/- Statements have type `Prop` and predicates on `A` have type `A → Prop`. -/
#check 3 < π
#check (Nat.Prime)


/- To prove a statement, you use *tactics* to construct a proof of that statement.
Tactics we've seen so far:
* `rfl`
* `rw`
* `ring`
* `calc`
-/

example : 2 + 2 = 4 := by rfl

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by ring




/- ## Implications
We will start with reasoning with implications in Lean.
-/

/-
**Forwards Reasoning** is reasoning forwards from the hypotheses that other facts must hold.
We can do this with the `have` tactic.
`intro` is used to introduce assumptions.
`exact` or `assumption` can be used to finish the proof.
-/

example (p q r : Prop) (hq : p → q) (hr : p → q → r) : p → r := by {
  sorry
  }

/- We can also use `specialize` to apply a hypothesis to arguments. -/
example (p q r : Prop) (hq : p → q) (hr : p → q → r) : p → r := by {
  sorry
  }

/-
**Backwards reasoning** is where we chain implications backwards,
deducing what we want to prove from a combination of other statements
(potentially even stronger ones).
We do this with the `apply` tactic.
-/

example (p q r s : Prop) (hq : p → s → q) (hr : q → r) : s → p → r := by {
  sorry
  }

/- We can also use `exact` or `refine` with more complicated proof terms. -/
example (p q r : Prop) (hq : p → p → q) (hr : q → r) : p → r := by {
  sorry
  }


/-
# Difference between `rw` and `apply`
- `rw` can be used to rewrite a subexpression (almost) anywhere in the goal,
  `apply` has to match the outermost thing you are trying to prove.
- *generally* you use `rw` with an equality,
  and `apply` with implications and "for all" statements.
-/


/- Often we can `apply` lemmas from Mathlib. -/
variable (f g : ℝ → ℝ)
#check (Continuous.add : Continuous f → Continuous g → Continuous (fun x ↦ f x + g x))

example : Continuous (fun x ↦ 2 + x * Real.sin x) := by {
  sorry
  }


/- # Finding Lemmas -/

/-
* Use tactics with a question mark to find a lemma.
  - `exact?` tries to apply a *single* lemma from the library to prove the current goal.
  - `apply?` tries to find all lemmas that can be used with `apply` to the current goal.
  - `rw?` tries to find all lemmas that can be used with `rw` to the current goal.
  - `have? using h1 h2` tries to find all facts that can be concluded from
    a single lemma using h1 and h2.
  - `simp?` simplifies the goal using `simp` and prints all used lemmas.

* Use `#leansearch "<query>."` to query theorems in natural language.
  Or use its website https://leansearch.net/

* Use `#loogle <query>` to query using syntactic searches
  The website https://loogle.lean-lang.org/ contains many search examples

* Guess the name of the lemma
  - You can search lemmas in the API documentation:
    https://leanprover-community.github.io/mathlib4_docs/
  - When typing a name, a list of suggested completions automatically shows up
  - You can also press `ctrl-space` (or `cmd-space` on a Mac) to see the list of suggestions.
  - Pressing `ctrl-space` toggles the display of the documentation of the selected completion.
  - You can also press `ctrl-T` (or `cmd-T`) to search for a lemma name (choosing an option shows you where it is proven)

  Some naming conventions:
  - a theorem named `A_of_B_of_C` establishes something of the form `A`
    from hypotheses of the form `B` and `C`.
  - `A`, `B`, and `C` approximate the way we might read the statement out loud.
  - Example: a theorem showing `x + y ≤ ...` will probably start with `add_le`.
    After typing `add_le` the autocomplete will give you some helpful choices.

* You can browse Mathlib
If you ctrl-click on a definition or theorem in VS Code you will jump
to the file where the theorem is proven.
You can often find similar theorems nearby the theorem you searched for.
-/

example (a b x y : ℝ) (h : a < b) (h3 : x ≤ y) : a + exp x < b + exp y := by {
  sorry
  }


/- In the following lemma, notice that `a`, `b`, `c`
are inside curly braces `{...}`.
This means that these arguments are *implicit*:
they don't have to be stated, but will be figured out by Lean automatically. -/

lemma cancel_addition {a b c : ℝ} (h : a + b = a + c) : b = c :=
    add_left_cancel h

example {b c : ℝ} (h : 2 + b = 2 + c) : b = c := by
  exact cancel_addition h

/- {G : Type*} and [Group G] are both implicit arguments.
The difference will be discussed later. -/
#check mul_right_inv


/- # Orders -/

section Real
variable {a b c d e x y z : ℝ}

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)


/- We can apply these lemmas manually, or use the `rfl`/`trans`/`calc` tactics. -/

example (x : ℝ) : x ≤ x := by exact le_refl x
example (x : ℝ) : x ≤ x := by apply le_refl
example (x : ℝ) : x ≤ x := by rfl

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  calc a
      = b := h₀
    _ < c := h₁
    _ ≤ d := h₂
    _ < e := h₃

/- `linarith` can prove inequalities (and equalities)
  that follow from linear combinations of assumptions. -/

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by {
  sorry
  }

example (x y z : ℝ) (hx : x ≤ 3 * y) (h2 : ¬ y > 2 * z)
    (h3 : x ≥ 6 * z) : x = 3 * y := by {
  sorry
  }


/- mathlib has lemmas that all common operations are monotone. Here are a few examples. -/

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check (mul_le_mul_of_nonneg_right : b ≤ c → 0 ≤ a → b * a ≤ c * a)

example (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 ≤ c) : a * (b + 2) ≤ (a + c) * (b + 2) := by {
  sorry
  }

/- `gcongr` is very convenient for monotonicity of functions. -/

example (h : a ≤ b) (h2 : b ≤ c) : exp a ≤ exp c := by {
  sorry
  }

example (h : a ≤ b) : c - exp b ≤ c - exp a := by {
  sorry
  }

example (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 ≤ c) : a * (b + 2) ≤ (a + c) * (b + 2) := by {
  sorry
  }

/- Remark: for equalities, you should use `congr` instead of `gcongr` -/

example (h : a = b) : c - exp b = c - exp a := by {
  sorry
  }


/- ## If and only if
* You can use `constructor` to prove an "if and only if" statement
* To use an "if and only if" statement `h`, you can use any of the following
  - `apply h.1`
  - `apply h.2`
  - `rw [h]`
  - `rw [← h]`
-/



#check exp_le_exp
#check (exp_le_exp.1 : exp a ≤ exp b → a ≤ b)
#check (exp_le_exp.2 : a ≤ b → exp a ≤ exp b)

example (h : a ≤ b) : exp a ≤ exp b := by {
  sorry
  }

example (h : a ≤ b) : exp a ≤ exp b := by {
  sorry
  }

example (h : exp a ≤ exp b) : a ≤ b := by {
  sorry
  }

example (h : exp a ≤ exp b) : a ≤ b := by {
  sorry
  }

example {p q : Prop} (h1 : p → q) (h2 : q → p) : p ↔ q := by {
  sorry
  }

/- ## Universal quantification
The tactics for universal quantification and implication are the same.
* We can use `intro` to prove an universal quantification (or implication).
* We can use `apply` or `specialize` to use a hypothesis
  that is a universal quantification (or implication). -/


def Injective (f : ℝ → ℝ) : Prop := ∀ x y : ℝ, f x = f y → x = y


example (f g : ℝ → ℝ) (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := by {
  sorry
  }


/- ## Conjunction

In Lean the conjunction of two statements `P` and `Q` is denoted by `P ∧ Q`, read as "P and Q".

We can use a conjunction as follows:
* If `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`.
* To prove `P ∧ Q` use the `constructor` tactic.
Note that this is the same as for `↔`.

Furthermore, we can decompose conjunction and equivalences.
* If `h : P ∧ Q`, the tactic `obtain ⟨hP, hQ⟩ := h`
  gives two new assumptions `hP : P` and `hQ : Q`.
* If `h : P ↔ Q`, the tactic `obtain ⟨hPQ, hQP⟩ := h`
  gives two new assumptions `hPQ : P → Q` and `hQP : Q → P`.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  sorry
  }

end Real
