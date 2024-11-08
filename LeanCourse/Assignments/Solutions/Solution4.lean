import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  constructor
  · intro h x
    rw [h]
    apply mem_univ
  · intro h
    ext x
    simp [h]
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  by_contra h
  apply h
  right
  intro h2
  apply h
  left
  assumption
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  ext
  · norm_num
  · ring
  }

-- NB: the following proof without an explicit use of `ext` works as well
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  norm_num -- or `simp`
  ring
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  have h1 : ℤ × ℕ ≃ ℕ := Denumerable.eqv (ℤ × ℕ) -- via `exact?`
  have h2 : ℤ × ℤ ≃ ℕ := Denumerable.eqv (ℤ × ℤ) -- via `exact?`
  exact h1.arrowCongr h2 -- via `exact?`
  }


/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  use fun i ↦ Classical.choose (hC i)
  intro i
  exact Classical.choose_spec (hC i)
  }


/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  obtain ⟨K, hK⟩ := hr N
  use K
  intro n hn
  apply hN
  apply hK
  assumption
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  intro ε hε
  obtain ⟨N, hN⟩ := hs₁ ε hε
  obtain ⟨N', hN'⟩ := hs₃ ε hε
  use max N N'
  intro n hn
  specialize hN n (le_of_max_le_left hn)
  specialize hN' n (le_of_max_le_right hn)
  rw [abs_lt] at *
  constructor
  · linarith [hs₁s₂ n]
  · linarith [hs₂s₃ n]
  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
  ext y
  constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  · rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
    exact ⟨⟨x, xs, rfl⟩, fxv⟩
  }


/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext x
  simp
  -- The rhs is now already broken down as much as we need it to, so let's tackle the lhs.
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
  --
  -- You could find this lemma with `rw?` (first suggestion) or when searching with loogle for `"_ ^ 2 ≤ _ ^ 2"`
  rw [sq_le_sq]
  --
  -- You could find this lemma with `rw?` or when searching with leansearch for `|4| ≤ |x| → x ≤ -4 ∨ 4 ≤ x`
  rw [le_abs']
  --
  -- An now we just need to `simp` away `|4|` and we're left with a tautology.
  simp
  }

-- Compact version of the proof above, using a single `simp` call:
lemma preimage_square' :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext x
  simp [show (16 : ℝ) = 4 ^ 2 by norm_num, sq_le_sq, le_abs']
  }

/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  use fun y ↦ if ok : ∃ x ∈ s, f x = y then choose ok else default
  intro x xmems
  have ok : ∃ x' ∈ s, f x' = f x := by use x
  simp [ok]
  show choose ok = x
  obtain ⟨mems, hfx⟩ := choose_spec ok
  apply hf
  all_goals assumption
  }


/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  have h1' : ∀ x y, f x ≠ g y := by {
    intro x y h
    have : g y ∈ range f ∩ range g := ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
    rw [h1] at this
    contradiction
    }
  have h1'' : ∀ y x, g y ≠ f x := by {
    intro x y
    symm
    apply h1'
    }
  have h2' : ∀ x, x ∈ range f ∪ range g := by {
    rw [h2]
    tauto
    }
  let L : Set α × Set β → Set γ := fun (x, y) ↦ f '' x ∪ g '' y
  let R : Set γ → Set α × Set β := fun s ↦ (f ⁻¹' s, g ⁻¹' s)
  use L, R
  constructor
  · ext s z
    simp [L]
    rcases h2' z with ⟨x,rfl⟩|⟨x,rfl⟩
    · simp [h1'', hf.eq_iff]
    · simp [h1', hg.eq_iff]
  · ext s z
    · simp [L, h1'', hf.eq_iff]
    · simp [L, h1', hg.eq_iff]
  }
