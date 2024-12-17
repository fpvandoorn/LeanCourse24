import LeanCourse.Common

open Set
noncomputable section





/-
# Practical remarks
* Assignment 10 does not require you to hand-in anything.
Work on your project instead.
-/

/- ## Last Week -/

/-
Last time we discussed differential geometry:
* `PartialHomeomorph` is used to specify a single chart;
* `ChartedSpace (Fin n → ℝ) M` states that `M` is locally `ℝⁿ`;
* `SmoothManifoldWithCorners (𝓡 n) M` states that the
  coordinate changes of `M` are smooth.
-/




/- ## Today: Formalization tips / pitfalls -/



/- Take a look at the tactic cheatsheet -/



/- Do not use the `have` tactic for data! -/

example (a b : ℕ) : (a + b) + a ≤ 2 * (a + b) := by
  have c := a + b
  have h : c = a + b := sorry -- not provable
  sorry

example (a b : ℕ) : (a + b) + a ≤ 2 * (a + b) := by
  have hR : Mul ℝ := by infer_instance
  -- the line above states that we have a multiplication
  -- on ℝ, but forget how it is defined.
  have h (x y : ℝ) : x * y = y * x :=
    mul_comm x y -- error
  sorry




/- `rw` doesn't rewrite under binders (∀, ∃, ∫, ∑, ...)
`simp_rw` does. -/
example {p q : ℕ → Prop} (h : ∃ x, p x)
    (h2 : ∀ x, p x ↔ q x) : ∃ x, q x := by
  -- rw [h2] at h
  sorry




/- `simp_rw` and `simp` cannot create goals for side-conditions.
You should specify which side conditions to use. -/
example {f : ℕ → ℕ} {p : ℕ → Prop}
    (h : ∀ x, p x → f x = x) :
    ∀ x, p x → f (f x) = x := by
  intros x hx
  -- simp_rw [h]
  -- simp [h]
  sorry




/- Try to break up long proofs into smaller lemmas.
Especially when you define something in a proof:
- define it as a separate definition
- then prove some easy properties about it
- it can be useful to write some simp-lemmas
-/


@[simp]
def myFun (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => 2 ^ myFun n + 1

example : ∃ (f : ℕ → ℕ), ∀ n, f (n + 1) > 2 ^ f n := by
  use myFun
  intro n
  simp

/- If you want to refer to an "inaccessible name",
i.e. a name with a dagger (†),
you can use `rename_i x y z` to give them a name.
-/
example : ∀ n : ℕ, 0 ≤ n := by
  intro
  rename_i n
  exact zero_le n


/- You can use `#lint` and Lean will check if you made some
common errors in your file.
(It will also point out that every definition
should have a documentation string, but you can ignore this). -/

@[simp]
lemma mul_sub_self_eq_zero (n m : ℕ) :
    n * (m - m) = 0 := by simp

#lint

/- You can `import Mathlib` in your project
to import everything.

Sometimes Lean runs a bit faster if you import less things.
You can run `#min_imports` to ask Lean for the
minimal imports needed for what you've done so far. -/

#min_imports




/- ## Defining your own notation (or tactics). -/

/- Notation in Lean is extensible.
You can define your own notation.
Here is a simple example. -/

notation "𝔽₂" => ZMod 2

example (n : 𝔽₂) : n + n = 0 := by
  rw [CharTwo.add_self_eq_zero]





/- Here we define our own infix notation,
the `:65` specifies the *precedence* of the notation.
Multiplication has higher precedence than addition.

You can see the default precedences by jumping to its definition.
Notation is also used by the pretty printer
-/

section CustomNotation

#check 1 + 1
local infix:65 " +' " => HAdd.hAdd
#eval 3 +' 5 * 2
#check 1 + 1

#check 3 + 5


/- You can declare notation with multiple meanings.
In this case the notation will be overloaded.
You can also override notation by setting a priority, e.g.
`(priority := high)` -/
#check ℤ ⊕ ℕ
local infix:30 " ⊕ " => HAdd.hAdd
#check 2 ⊕ 3
#check ℤ ⊕ ℕ

end CustomNotation


/- You can also define more complicated notations,
such as notation that binds a variable. -/
notation3 "do_twice" (...) " ↦ "
  c:60:(scoped f => f) => c ∘ c

#check do_twice (x : ℕ) ↦ x ^ 2
#check (do_twice x ↦ x ^ 2) 3
#eval (do_twice x ↦ x ^ 2) 3


/- If you want to declare your own notation,
I recommend copying and modifying an
existing notation declaration from Mathlib. -/



/- You can declare macros to combine some simple tactics.
`(...) stands for "quotation".
It reflects terms/tactics/commands into Syntax objects. -/

macro "split_iff" : tactic => `(tactic| constructor <;> intro h)
macro "quit" : tactic => `(tactic| all_goals sorry)

example : 2 + 2 = 5 ↔ 5 < 6 := by
  split_iff
  quit



/-
`macro` is short for `syntax` + `macro_rules`.
You can declare multiple macro rules.
These will each be tried in reverse order,
until one of them succeeds.
-/

syntax (name := myName) "easy" : tactic

-- example : True := by easy

macro_rules | `(tactic|easy) => `(tactic|assumption)
macro_rules | `(tactic|easy) => `(tactic|focus (simp; first | done | easy))
macro_rules | `(tactic|easy) => `(tactic|focus (ring_nf; done))

example (n m : ℕ) (h : n ≠ m) : n ≠ m ∧ n + m = m + n ∧ 0 ≤ n := by
  refine ⟨?_, ?_, ?_⟩
  all_goals easy


/- Writing complete tactics from scratch is also possible,
but outside the scope of this course. -/
