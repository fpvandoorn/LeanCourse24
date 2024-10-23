import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 2, 3, 4 and 5
  Read chapter 3, sections 1, 4.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 22.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by {
  linarith
  }

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by {
  rw [← h1]
  ring
  }

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by {
  gcongr
  · linarith
  · linarith
  }

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by {
  constructor
  · intro
    linarith
  · intro
    linarith
  }

/- Note: for purely numerical problems, you can use `norm_num`
(although `ring` or `linarith` also work in some cases). -/
example : 2 + 3 * 4 + 5 ^ 6 ≤ 7 ^ 8 := by norm_num
example (x : ℝ) : (1 + 1) * x + (7 ^ 2 - 35 + 1) = 2 * x + 15 := by norm_num

/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example (x : ℝ) (hx : x = 3) : x ^ 2 + 3 * x - 5 = 13 := by
  rw [hx]
  norm_num

example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by {
  calc
    n - m ^ 2 ≤ n - 0 := by gcongr; exact sq_nonneg m
    _ ≤ n + 3 := by linarith
  }

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by {
  specialize h 2
  norm_num at h
  exact h
  }

example {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ} (h₁₂ : a₁ + a₂ + 1 ≤ b₁ + b₂) (h₃ : a₃ + 2 ≤ b₃) :
  exp (a₁ + a₂) + a₃ + 1 ≤ exp (b₁ + b₂) + b₃ + 1 := by {
  gcongr exp ?_ + ?_ + 1
  · linarith
  · linarith
  }


/- Divisibility also gives an order. Warning: divisibility uses a unicode character,
which can be written using `\|`. -/

/-- Prove this using calc. -/
lemma exercise_division (n m k l : ℕ) (h₁ : n ∣ m) (h₂ : m = k) (h₃ : k ∣ l) : n ∣ l := by {
  calc
    n ∣ m := h₁
    _ = k := h₂
    _ ∣ l := h₃
  }


/- We can also work with abstract partial orders. -/

section PartialOrder

variable {X : Type*} [PartialOrder X]
variable (x y z : X)

/- A partial order is defined to be an order relation `≤` with the following axioms -/
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

/- every preorder comes automatically with an associated strict order -/
example : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

/- the reverse order `≥`/`>` is defined from `≤`/`<`.
In Mathlib we usually state lemmas using `≤`/`<` instead of `≥`/`>`. -/
example : x ≥ y ↔ y ≤ x := by rfl
example : x > y ↔ y < x := by rfl


example (hxy : x ≤ y) (hyz : y ≤ z) (hzx : z ≤ x) : x = y ∧ y = z ∧ x = z := by {
  have h1 : x = y := le_antisymm hxy (hyz.trans hzx)
  rw [h1] at hzx ⊢
  have h2 : y = z := le_antisymm hyz hzx
  rw [h2]
  tauto
  --
  -- NB: Alternatively, instead of finishing by `tauto`:
  --constructor
  --· rfl
  --constructor
  --· rfl
  --· rfl
  }


end PartialOrder


/-! # Exercises to hand-in. -/

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by {
  calc
    t ^ 2 - 3 * t - 17 = t * (t - 3) - 17 := by ring
      _ ≥ 10 * (10 - 3) - 17 := by gcongr
      _ ≥ 5 := by norm_num
  }


/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by {
  calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2
      = (t ^ 2 + 3 * t + 1) * (t ^ 2 - 4) + 10 * t + 2 := by ring
    _ = (t ^ 2 + 3 * t + 1) * 0 + 10 * t + 2 := by rw [ht]
    _ = 10 * t + 2 := by ring
  }

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by {
  calc
    n + 1 = 0 + n + 1 := by ring
    _ ≤ m ^ 2 + n + 1 := by gcongr; exact sq_nonneg m
    _ ≤ 3 + 0 := by linarith
    _ ≤ 3 + k ^ 2 := by gcongr; exact sq_nonneg k
  }



section Min
variable (a b c : ℝ)

/- The following theorems characterize `min`.
Let's this characterization it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a :=
  have h : {x y : ℝ} -> min x y ≤ min y x := by {
    intros x y
    apply le_min
    · exact min_le_right x y
    exact min_le_left x y
    }
  le_antisymm h h

-- Alternatively:
lemma exercise_min_comm' : min a b = min b a := by {
  apply le_antisymm
  · apply le_min
    · exact min_le_right a b
    · exact min_le_left a b
  · apply le_min
    · exact min_le_right b a
    · exact min_le_left b a
  }

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by {
  apply le_antisymm
  · apply le_min
    apply le_min
    · apply min_le_left
    -- NB: We can control the proof state by explictly stating the type of the
    -- placeholders. If we don't do this, the chosen middle term for
    -- transitivity depends on the rest of the proof. You can try this out
    -- by commenting out the rest of the line after `le_trans` and looking
    -- at the tactic state.
    · apply le_trans (?_ : min a (min b c) ≤ min b c) (?_ : min b c ≤ b)
      apply min_le_right
      apply min_le_left
    apply le_trans ?_ (?_ : min b c ≤ c)
    apply min_le_right
    apply min_le_right
  apply le_min
  -- NB: We can also control the proof state by explicitly stating what the
  -- "middle" term is. In the statement of `le_trans` it is called
  -- `b`; do not confuse this with our local `b` here!
  · apply le_trans (b := min a b)
    apply min_le_left
    apply min_le_left
  apply le_min
  -- And here's another way of controlling the tactic state:
  · apply @le_trans _ _ _ (min a b)
    apply min_le_left
    apply min_le_right
  apply min_le_right
  }

end Min

/- Prove that the following function is continuous.
You can use `Continuous.div` as the first step,
and use the search techniques to find other relevant lemmas.
`ne_of_lt`/`ne_of_gt` will be useful to prove the inequality. -/
lemma exercise_continuity : Continuous (fun x ↦ (sin (x ^ 5) * cos x) / (x ^ 2 + 1)) := by {
  apply Continuous.div
  · apply Continuous.mul
    -- NB: if you're not careful with applying `Continuous.comp`,
    -- you can end up with `Continuous Complex.re` as a goal, which
    -- is not really productive. For some other options for how to control
    -- the tactic state, see the solution for `exercise_min_assoc`.
    · apply Continuous.comp continuous_sin (continuous_pow 5)
    · exact continuous_cos
  · exact Continuous.add (continuous_pow 2) continuous_const
  · intro x
    apply ne_of_gt
    -- NB: Instead of the calculation at the end of the proof, you could also use `nlinarith`:
    have h : 0 < x ^ 2 + 1 := by nlinarith
    calc
      0 ≤ x ^ 2 := sq_nonneg x
      _ < x ^ 2 + 1 := by norm_num
  }

/- Prove this only using `intro`/`constructor`/`obtain`/`exact` -/
lemma exercise_and_comm : ∀ (p q : Prop), p ∧ q ↔ q ∧ p := by {
  intro p q
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := h
    constructor
    · exact hq
    · exact hp
  · intro h
    obtain ⟨hq, hp⟩ := h
    constructor
    · exact hp
    · exact hq
  }


/-- Prove the following properties of nondecreasing functions. -/
def Nondecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

lemma exercise_nondecreasing_comp (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  unfold Nondecreasing at hf hg ⊢
  intro x y hxy
  specialize hf x y hxy
  specialize hg (f x) (f y) hf
  rw [Function.comp, Function.comp]
  exact hg
  }

-- Alternative solution:
lemma exercise_nondecreasing_comp' (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  intro _ _ h
  apply hg
  apply hf
  exact h
  }


/-- Note: `f + g` is the function defined by `(f + g)(x) := f(x) + g(x)`.
  `simp` can simplify `(f + g) x` to `f x + g x`. -/
lemma exercise_nondecreasing_add (f g : ℝ → ℝ) (hf : Nondecreasing f) (hg : Nondecreasing g) :
    Nondecreasing (f + g) := by {
  intro x y hxy
  simp
  gcongr
  · apply hf
    assumption
  · apply hg
    assumption
  }



/-- Prove the following property of even. -/
def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

lemma exercise_even_iff (f g : ℝ → ℝ) (hf : EvenFunction f) :
    EvenFunction (f + g) ↔ EvenFunction g := by {
  constructor
  · intro hfg x
    specialize hfg x
    simp at hfg
    calc
      g x = f x + g x - f x := by ring
      _ = (f (-x) + g (-x)) - f (-x) := by rw [hfg, hf x]
      _ = g (-x) := by ring
  · intro hg x
    simp
    rw [hf, hg]
  }
