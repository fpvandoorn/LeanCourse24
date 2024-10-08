import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real

/-

* Make sure to follow the instructions in the README to install Lean and set up this repository locally.

* Register on Basis and eCampus

* Read chapter 1 and sections 2.1 and 2.2 in Mathematics in Lean.
  https://leanprover-community.github.io/mathematics_in_lean

* You do not need to hand-in anything this week.

* Do the exercises below, by replacing each `sorry` with tactics.

* Do the following exercises:
  - `LeanCourse/MIL/C02_Basics/S01_Calculating.lean`
  - `LeanCourse/MIL/C02_Basics/S02_Proving_Identities_in_Algebraic_Structures.lean`
  There are solutions in the solution folder in case you get stuck.
  Note that the exercises only make sense while reading the chapter at the same time,
  so make sure you open mathematics in Lean in a browser.

-/



/-
# Computing

## The ring tactic

One of the earliest kind of proofs one encounters while learning mathematics is proving by
a calculation. It may not sound like a proof, but this is actually using lemmas expressing
properties of operations on numbers. Of course we usually don't want to invoke those explicitly
so mathlib has a tactic `ring` taking care of proving equalities that follow by applying
the properties of all commutative rings.
-/


example (a b c : ℝ) : (a * b) * c = b * (a * c) := by {
  ring
  }

/- It's your turn, replace the word sorry below by a proof. In this case the proof is just `ring`.
After you prove something, you will see a small "No goals" message, which is the indication that
your proof is finished.
-/

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by {
  sorry
  }

/- In the first example above, take a closer look at where Lean displays parentheses.
The `ring` tactic certainly knows about associativity of multiplication, but sometimes
it is useful to understand that binary operation really are binary and an expression like
`a*b*c` is read as `(a*b)*c` by Lean and the fact that is equal `a*(b*c)` is a lemma
that is used by the `ring` tactic when needed.
-/


/-
## The rewriting tactic

Let us now see how to compute using assumptions relating the involved numbers.
This uses the fundamental property of equality: if two
mathematical objects A and B are equal then, in any statement involving A, one can replace A
by B. This operation is called rewriting, and the Lean tactic for this is `rw`.
Carefully step through the proof below and try to understand what is happening.
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h]
  rw [h']
  ring
  }

/-
Note the `rw` tactic changes the current goal. After the first line of the above proof,
the new goal is `b + c + e = d + c`. So you can read this first proof step as saying:
"I wanted to prove, `a + e = d + c` but, since assumption `h` tells me `a = b + c`,
it suffices to prove `b + c + e = d + c`."

One can actually do several rewritings in one command.
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by {
  rw [h, h']
  ring
  }

/-
Note that putting your cursor between `h` and`h'` shows you the intermediate proof state.

Note also the subtle background color change in the tactic state that show you in green
what is new and in red what is about to change.

Now try it yourself. Note that `ring` can still do calculations,
but it doesn't use the assumptions `h` and `h'`
-/

example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by {
  sorry
  }

/- ## Rewriting with a lemma

In the previous examples, we rewrote the goal using a local assumption. But we can
also use lemmas. For instance let us prove a lemma about exponentiation.
Since `ring` only knows how to prove things from the axioms of rings,
it doesn't know how to work with exponentiation.
For the following lemma, we will rewrite with the lemma
`exp_add x y` twice, which is a proof that `exp(x+y) = exp(x) * exp(y)`.
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add (a + b) c]
  rw [exp_add a b]
  }

/-
Note also that after the second `rw` the goal becomes
`exp a * exp b * exp c = exp a * exp b * exp c` and Lean immediately declares the proof is done.

If we don't provide arguments to the lemmas, Lean will rewrite the first matching
subexpression. In our example this is good enough. Sometimes more control is needed.
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by {
  rw [exp_add, exp_add]
  }

/-
Let's do an exercise, where you also have to use
`exp_sub x y : exp(x - y) = exp(x) / exp(y)` and `exp_zero : exp 0 = 1`.

Recall that `a + b - c` means `(a + b) - c`.

You can either use `ring` or rewrite with `mul_one x : x * 1 = x` to simplify the denominator on the
right-hand side.
-/

example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by {
  sorry
  }


/- Prove the following equality just by using `rw`.
The two lemmas below express the associativity and commutativity of multiplication. -/

#check (mul_assoc : ∀ a b c : ℝ, a * b * c = a * (b * c))
#check (mul_comm : ∀ a b : ℝ, a * b = b * a)

example (a b c : ℝ) : a * b * c = b * (a * c) := by {
  sorry
  }




/-
In the following lemma the commutator of two elements of a group is defined as
`⁅g, h⁆ = g * h * g⁻¹ * h⁻¹`. Prove the lemma below just by using `rw`.

The `variable` command below can be read as "let `G` be a group and `g` and `h` elements of `G`"
The precise meaning of this line will be discussed in later classes.
-/

section
variable {G : Type*} [Group G] (g h : G)

#check commutatorElement_def g h
#check mul_inv_rev g h
#check inv_inv g

lemma inverse_of_a_commutator : ⁅g, h⁆⁻¹ = ⁅h, g⁆ := by {
  sorry
  }

end

/-
## Rewriting from right to left

Since equality is a symmetric relation, we can also replace the right-hand side of an
equality by the left-hand side using `←` as in the following example.
-/
example (a b c : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by {
  rw [← h, h']
  }

/-
Whenever you see in a Lean file a symbol that you don't see on your keyboard, such as ←,
you can put your mouse cursor above it and learn from a tooltip how to type it.
In the case of ←, you can type it by typing "\l ", so backslash-l-space.

Note this rewriting from right to left story is all about sides in the equality you want to
*use*, not about sides in what you want to *prove*. The `rw [← h]` will replace the right-hand side
by the left-hand side, so it will look for `b + c` in the current goal and replace it with `a`.
-/

example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by {
  sorry
  }

example (a b c d : ℝ) (h : a*d - 1 = c) (h' : a*d = b) : c = b - 1 := by {
  sorry
  }

/- ## Rewriting in a local assumption

We can also perform rewriting in an assumption of the local context, using for instance
  `rw [exp_add x y] at h`
in order to replace `exp(x + y)` by `exp(x) * exp(y)` in assumption `h`.

The `exact` tactic allows you to give an explicit proof term to prove the current goal.
-/

example (a b c d : ℝ) (h : c = b + d*a) (h' : b = d + a) : c = d + a + d*a := by {
  rw [h'] at h
  -- Our assumption `h` is now exactly what we have to prove
  exact h
  }

/- ## Calculation layout using calc

What is written in the above example is very far away from what we would write on
paper. Let's now see how to get a more natural layout (and also return to using `ring`
instead of explicit lemma invocations).
After each `:=` below, the goal is to prove equality with the preceding line
(or the left-hand on the first line).
Carefully check you understand this by putting your cursor after each `by` and looking
at the tactic state.
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by {
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring
  }

/-
Let's do some exercises using `calc`. Feel free to use `ring` in some steps.
-/

example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by {
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by sorry
              _ = exp ((b + b) + (c + c))           := by sorry
              _ = exp (b + b) * exp (c + c)         := by sorry
              _ = (exp b * exp b) * (exp c * exp c) := by sorry
              _ = (exp b) ^ 2 * (exp c)^2           := by sorry
  }

/-
From a practical point of view, when writing such a proof, it is sometimes convenient to:
* pause the tactic state view update in VScode by clicking the Pause icon button
  in the top right corner of the Lean Infoview panel.
* write the full calculation, ending each line with ":= ?_"
* resume tactic state update by clicking the Play icon button and fill in proofs.

The underscores should be placed below the left-hand-side of the first line below the `calc`.
Aligning the equal signs and `:=` signs is not necessary but looks tidy.
-/

/- Prove the following using a `calc` block. -/
example (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by {
  sorry
  }



/- Prove the following using a `calc` block. -/

example (a b c d : ℝ) : a + b + c + d = d + (b + a) + c := by
  sorry

/- Prove the following using a `calc` block. -/

#check sub_self

example (a b c d : ℝ) (h : c + a = b*a - d) (h' : d = a * b) : a + c = 0 := by {
  sorry
  }


/- A ring is a collection of objects `R` with operations `+`, `*`,
constants `0` and `1` and negation `-` satisfying the following axioms. -/
section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)


/- Use `calc` to prove the following from the axioms of rings, without using `ring`. -/

example {a b c : R} (h : a + b = a + c) : b = c := by {
  sorry
  }

end


/- Prove the following equalities using `ring` (recall that `ring` doesn't use local hypotheses). -/

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

example (a b c d : ℝ) (h1 : c = d * a + b) (h2 : b = a * d) : c = 2 * a * d := by {
  rw [h1, h2]
  ring
  }

/-
Do the following exercise using the `rw` tactic only.

The following lemmas may be useful.
-/

section
variable (a b c x : ℝ)

#check (pow_two x       : x^2 = x*x)
#check (mul_add a b c   : a*(b + c) = a*b + a*c)
#check (add_mul a b c   : (a + b)*c = a*c + b*c)
#check (mul_sub a b c   : a*(b - c) = a*b - a*c)
#check (sub_mul a b c   : (a - b)*c = a*c - b*c)
#check (add_sub a b c   : a + (b - c) = (a + b) - c)
#check (sub_add a b c   : a - b + c = a - (b - c))
#check (add_assoc a b c : (a + b) + c = a + (b + c))
#check (sub_sub a b c   : a - b - c = a - (b + c))
#check (sub_self a      : a - a = 0)
#check (add_zero a      : a + 0 = a)
#check (zero_add a      : 0 + a = a)

example : (a + b) * (a - b) = a^2 - b^2 := by sorry


-- Now redo it with `ring`.

example : (a + b) * (a - b) = a^2 - b^2 := by sorry

end
