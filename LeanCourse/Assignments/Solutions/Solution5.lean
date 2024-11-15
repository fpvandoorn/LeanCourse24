import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  -- simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)
  --sorry


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  norm_cast at h
  rw [h]
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  norm_cast at h ⊢
  calc
    n + 1 < n + 3 := by omega
    _ ≤ 2 * m := h
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  have : (n : ℝ) = m ^ 2 - 2 * m := by norm_cast at h ⊢
  rw [this]
  ring
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  norm_cast -- this also works: `exact cast_lt`
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  norm_cast
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  gcongr
  norm_cast
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  have : 0 < (n : ℝ) := by norm_cast
  exact sqrt_pos_of_pos this -- via `exact?`
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  ext
  simp
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  simp
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  rw [Finset.disjoint_left]
  intro x hxs hxt
  simp at hxt
  tauto
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  induction n with
  | zero => simp [fibonacci]
  | succ n ih =>
    simp [sum_range_succ, ih, fibonacci]
    rw [add_comm]
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  induction n with
  | zero => simp [fibonacci]
  | succ n ih =>
    simp [sum_range_succ, ih, fibonacci] -- you can also `rw` and then `push_cast`
    ring
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  induction n with
  | zero => simp
  | succ n ih =>
    simp [sum_range_succ _ (n + 1), mul_add 6, ih]
    ring
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  induction n with
  | zero => norm_num [fac]
  | succ n ih =>
    rw [fac, pow_add, mul_comm]
    gcongr
    omega
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  induction n with
  | zero => simp [fac]
  | succ k ih =>
    rw [fac, prod_range_succ, ← ih, mul_comm]
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    simp [fac, ih, prod_range_succ]
    ring
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here


/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

-- give definition here



/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β where
  toFun := fun ⟨x,y,z⟩ ↦ ⟨e x, e y, e z⟩
  invFun := fun ⟨x,y,z⟩ ↦ ⟨e.invFun x, e.invFun y, e.invFun z⟩
  left_inv := by simp [LeftInverse]
  right_inv := by simp [Function.RightInverse, LeftInverse]


/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

def Triple.add {α : Type*} [AbelianGroup' α] (a b : Triple α) : Triple α where
  x := AbelianGroup'.add a.x b.x
  y := AbelianGroup'.add a.y b.y
  z := AbelianGroup'.add a.z b.z

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) where
  add := Triple.add
  comm := by simp [Triple.add, AbelianGroup'.comm]
  assoc := by simp [Triple.add, AbelianGroup'.assoc]
  zero := ⟨AbelianGroup'.zero, AbelianGroup'.zero, AbelianGroup'.zero⟩
  add_zero := by simp [Triple.add, AbelianGroup'.add_zero]
  neg a := ⟨AbelianGroup'.neg a.x, AbelianGroup'.neg a.y, AbelianGroup'.neg a.z⟩
  add_neg := by simp [Triple.add, AbelianGroup'.add_neg]


/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here
structure StrictBipointed (α : Type) :=
  (here there : α)
  (strict : here ≠ there)

-- state and prove the lemma here
lemma StrictBipointed.ne_or_ne {α : Type} (X : StrictBipointed α) (x : α) :
    x ≠ X.here ∨ x ≠ X.there := by
  by_cases hx : x = X.here
  · subst hx
    right
    exact X.strict
  · left
    exact hx


/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
  have : ∀ n, (∑ i in range (n + 1), (i : ℚ)) = n * (n + 1) / 2
  · intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  rw [this]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  have lt_disjoint : ∀ i j, i < j → Disjoint (C i) (C j)
  · intro i j hij
    simp [Set.disjoint_left, hC]
    tauto
  constructor
  · intro i j hij
    obtain h|h := hij.lt_or_lt
    · exact lt_disjoint i j h
    · exact (lt_disjoint j i h).symm
  · apply subset_antisymm
    · gcongr with i
      rw [hC]
      exact diff_subset
    · simp [Set.subset_def, hC]
      intros x i hx
      obtain ⟨j, imem, hj⟩ := h { i | x ∈ A i } ⟨i, hx⟩
      use j
      tauto
  }

#check WellFoundedLT.induction
-- Alternate proof using wellfounded induction for the last part
lemma disjoint_unions' {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {

  have lt_disjoint : ∀ i j, i < j → Disjoint (C i) (C j)
  · intro i j hij
    simp [Set.disjoint_left, hC]
    tauto

  constructor
  · intro i j hij
    obtain h|h := hij.lt_or_lt
    · exact lt_disjoint i j h
    · exact Disjoint.symm (lt_disjoint j i h)

  · apply subset_antisymm
    · gcongr with i
      rw [hC]
      exact diff_subset -- via `exact?`
    · simp [Set.subset_def]
      intro x i xmem
      induction i using wf.induction with | _ i ih =>
      by_cases hx : ∃ j < i, x ∈ A j
      · obtain ⟨j, h1, h2⟩ := hx
        exact ih j h1 h2
      · simp [hC] at hx ⊢
        use i
  }


/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  rw [Nat.prime_def_lt']
  constructor
  · push_neg
    intro h
    rw [← or_assoc]
    by_cases h2 : n = 0 ∨ n = 1
    · left
      trivial
    · right
      have : 2 < n := by omega
      obtain ⟨a, ha, han, hadvd⟩ := h (by linarith)
      obtain ⟨b, hb⟩ := hadvd
      have : 2 ≤ b := by nlinarith
      use a, b
  · rintro (hn0|hn1|hn) h
    · linarith
    · linarith
    · obtain ⟨a, b, ha, hb, hab⟩ := hn
      have : a < n := by nlinarith
      have : a ∣ n := Dvd.intro b (hab.symm) -- via `exact?`
      tauto
  }

-- Here's an alternate proof through applying congruence rules manually.
lemma not_prime_iff' (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  rw [← or_assoc, ← Nat.le_one_iff_eq_zero_or_eq_one, ← not_lt, ← imp_iff_not_or, Nat.prime_def_lt',
    succ_le]
  push_neg
  simp
  apply imp_congr .rfl
  apply exists_congr
  intro k
  apply and_congr_right
  intro hk
  rw [dvd_def, ← exists_and_left]
  apply exists_congr
  intro l
  apply and_congr_left
  intro h
  subst h
  rw [succ_le]
  apply lt_mul_iff_one_lt_right
  linarith
  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp [not_prime_zero] at hn
  · norm_num at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul] -- via `rw?`
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by gcongr; exact Int.modEq_sub (2 ^ a) 1 -- via `exact?`
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by simp
  have h2 : 2 ^ 2 ≤ 2 ^ a := by gcongr; norm_num
  have h3 : 1 ≤ 2 ^ a := by linarith
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    gcongr
    · norm_num
    · nlinarith
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by gcongr; simp; simp
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  apply h4
  apply hn.2
  · exact h5
  · exact h'
  }

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  have : ∀ {a b : ℕ}, 0 < a → a ≤ b → ¬ IsSquare (b ^ 2 + a)
  · intro a b ha hab ⟨c, hc⟩
    have : b < c := by nlinarith
    have : c < b + 1 := by nlinarith
    linarith
  obtain h|h := le_total a b
  · exact .inr (this ha h)
  · exact .inl (this hb h)
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

def groupPosReal : Group PosReal where
  mul x y := ⟨x.1 * y.1, mul_pos x.2 y.2⟩
  mul_assoc x y z := mul_assoc x y z
  one := ⟨1, by norm_num⟩
  one_mul x := one_mul x
  mul_one x := mul_one x
  inv x := ⟨x.1⁻¹, inv_pos.mpr x.2⟩
  inv_mul_cancel x := by ext; apply inv_mul_cancel₀; exact x.2.ne'



/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] Finset.card_powerset
attribute [-simp] Multiset.card_powerset
#check Finset.induction

example (α : Type*) (s : Finset α) : Finset.card (powerset s) = 2 ^ Finset.card s := by {
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hxs ih =>
      rw [Finset.powerset_insert, Finset.card_union_of_disjoint, Finset.card_image_of_injOn,
        Finset.card_insert_of_not_mem hxs]
      · omega
      · intro t ht t' ht' htt'
        have or_congr_right_iff (p q r : Prop) : (p ∨ q ↔ p ∨ r) ↔ ((p → ¬ q ∧ ¬ r) → (q ↔ r)) := by
          tauto
        simp [Finset.ext_iff, or_congr_right_iff] at htt'
        ext y
        apply htt'
        rintro rfl
        simp at ht ht'
        constructor
        · exact fun hy ↦ hxs (ht hy)
        · exact fun hy ↦ hxs (ht' hy)
      · rw [Finset.disjoint_left]
        intro t ht h2t
        simp at ht h2t
        obtain ⟨t, h2t, rfl⟩ := h2t
        apply hxs
        apply ht
        exact mem_insert_self x t
  }
