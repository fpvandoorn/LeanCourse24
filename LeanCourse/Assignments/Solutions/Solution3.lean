import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
  use 0
  apply h
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  intro ⟨x, hx⟩
  use x
  exact h x hx
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
  constructor
  · intro h x hx
    apply h
    use x
  · intro h1 ⟨x, hx⟩
    exact h1 x hx
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
  constructor
  · intro ⟨x, ⟨hpx, hr⟩⟩
    exact ⟨⟨x, hpx⟩, hr⟩
  · intro ⟨⟨x, hpx⟩, hr⟩
    exact ⟨x, ⟨hpx, hr⟩⟩ -- or `use x`
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  constructor
  · intro ⟨x, hpx⟩ h
    apply h x
    exact hpx
  · intro h
    by_contra h'
    apply h
    intro x hpx
    apply h'
    use x
  }

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  intro ε hε
  use 0
  intros
  simp
  exact hε
  }

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
  calc
    (n)! ∣ (m)! := by exact factorial_dvd_factorial h -- from `exact?`
    _ ∣ (m + 1)! := by exact Dvd.intro_left m.succ rfl -- from `exact?`


section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  rintro z ⟨x, xmem, rfl⟩
  exact xmem
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  intro z zmems
  rcases h z with ⟨x, rfl⟩
  use x
  trivial
  }

-- Longer, more explicit version:
example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  intro z zmems
  rcases h z with ⟨x, fxeqz⟩
  show ∃ x, f x ∈ s ∧ f x = z
  use x
  constructor
  · rw [fxeqz]
    exact zmems
  · exact fxeqz
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  rintro z ⟨⟨x, mems, rfl⟩, ⟨y, memt, hxy⟩⟩
  rw [h hxy] at memt
  use x
  trivial
  }

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by {
  ext z; simp
  constructor
  · rintro ⟨x, ⟨i, xmemAi⟩, rfl⟩
    use i, x
  · rintro ⟨i, x, xmemAi, rfl⟩
    use x
    simp
    use i
  }

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  ext z; simp
  constructor
  · rintro ⟨y, rfl⟩
    exact sq_nonneg y
  · intro znonneg
    exact ⟨sqrt z, sq_sqrt znonneg⟩
  }

end Set

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  · rintro ⟨x, hp | hq⟩
    · left; use x
    · right; use x
  · rintro (⟨x,hp⟩|⟨x,hq⟩)
    · use x; left; exact hp
    · use x; right; exact hq
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  unfold SurjectiveFunction
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    use f x
    exact hx
  · intro hg z
    obtain ⟨y, hy⟩ := hg z
    obtain ⟨x, hx⟩ := hf y
    use x
    simp
    rw [← hy, ← hx]
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  intro y
  simp -- just for readability
  obtain ⟨x', hx'⟩ := hf ((y - 1) / 2)
  have : 1 + f x' * 2 = y := by rw [hx']; ring
  use x' / 3 - 4
  ring
  exact this
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  intro fsurj
  let R := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := fsurj R
  by_cases h : x ∈ R
  · have : ¬ x ∈ f x := by trivial
    rw [hx] at this
    contradiction
  · have : x ∈ f x := not_mem_compl_iff.mp h -- via `exact?`
    rw [hx] at this
    contradiction
  }

-- Alternatively:
lemma exercise_cantor' (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  intro fsurj
  let R := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := fsurj R
  have : x ∈ f x ↔ ¬ x ∈ f x
  · nth_rw 1 [hx]
    rfl
  have h2 : ¬ x ∈ f x
  · intro h
    exact this.1 h h
  apply h2
  apply this.2 h2
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  unfold SequentialLimit
  intro ε hε
  have : ε / 2 > 0 := by positivity -- or via `exact?`: `exact half_pos hε`
  obtain ⟨Ns, hNs⟩ := hs (ε / 2) this
  obtain ⟨Nt, hNt⟩ := ht (ε / 2) this
  use max Ns Nt
  intro n hn
  simp
  calc |s n + t n - (a + b)|
      = |(s n - a) + (t n - b)| := by ring
    _ ≤ |s n - a| + |t n - b| := by apply abs_add
    _ < ε / 2 + ε / 2 := by
        specialize hNs n (le_of_max_le_left hn)  -- via `(by exact?)`
        specialize hNt n (le_of_max_le_right hn) -- via `(by exact?)`
        gcongr -- uses specialized `hNs` and `hNt`
    _ = ε := by ring
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := abs_mul c (s n - a) -- via `exact?`
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1 -- via `exact?`
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel₀ ε (by positivity)
  }


section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  intro k
  use k
  intro n hn
  simp
  gcongr
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  intro k
  obtain ⟨N₁, hN₁⟩ := h₁ k
  obtain ⟨N₂, hN₂⟩ := h₂ k
  use N₁ + N₂
  intro n hn
  simp
  rw [mul_add]
  gcongr
  · exact hN₁ n (by linarith)
  · exact hN₂ n (by linarith)
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  use fun n ↦ n ^ n
  constructor
  · intro k
    use k
    intro n hn
    simp
    calc k * n ^ n ≤ n * n ^ n := by gcongr
      _ = n ^ (n + 1) := by ring
      _ ≤ (n + 1) ^ (n + 1) := by gcongr; simp
  · intro n
    exact pow_self_ne_zero n -- via `exact?`, or use `positivity`
  }

-- Alternate solution:
lemma eventuallyGrowsFaster_shift' : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  use fun n ↦ (n)!
  constructor
  · intro k
    use k
    intro n hn
    simp
    calc k * n ! ≤ n * n ! := by gcongr
      _ ≤ (n + 1) * n ! := by {
          gcongr
          exact Nat.le_add_right n 1 -- via `exact?`
        }
      _ = (n + 1)! := by rfl
  · intro n
    exact factorial_ne_zero n -- via `exact?`, or use `positivity`
  }

end Growth
