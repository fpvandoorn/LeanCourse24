import LeanCourse.Common
open Real Function Set
noncomputable section





/-
# Practical remarks
* Assignment 5 due on 5.12. Upload it to eCampus.
-/

/- # Last Week -/

/-
Last time we discussed sets:
* Set-builder notation: `{ x : X | p x}`;
* Unions/intersections: `⋃ i : ι, C i`, `⋃ i ∈ s, C i` or `⋃₀ C`;
* Preimages and images: `f ⁻¹' s` or `f '' s`;

We also discussed choice:
* A global choice principle is given by `Classical.choose` and `Classical.choose_spec`
* We used it to define the inverse of a function.

-/


/- # Today: Numbers and Structures -/


/-
Some useful tactics when dealing with numbers:
* `norm_num`: compute equalities and inequalities involving numerals
* `omega`: can do linear arithmetic (usually better than `linarith`) on `ℕ` and `ℤ`.
* `positivity`: can show that something is positive/non-negative
  by using that its components are positive/non-negative.
* `field_simp` can simplify divisions (often useful before ring).
-/

example : 2 ^ 3 + 17 = 300 / 12 := by norm_num
example (x : ℝ) : x + 5 + 3 = x + 8 := by
  rw [add_assoc]
  norm_num

example (n m : ℤ) : 2 * n + 1 ≠ 2 * m := by omega

example (n m k : ℤ) (hn : 0 < n) (hm : 0 ≤ m) (hk : 0 < k) : 0 < n * m + k  := by positivity
example (n m k : ℝ) (hn : 0 < n) (hm : 0 ≤ m) (hk : 0 < k) : 0 < n * m + k  := by positivity

example (x y : ℝ) (hy : y ≠ 0) : 2 * x / y + 1 + x * y = (2 * x + y) / y + y * x := by
  field_simp [hy]
  ring



/- **Warning**
Division and subtraction of natural numbers again returns a natural number.
This is division rounded down and truncated subtraction.
-/

#eval 9 / 3
#eval 10 / 3
#eval 11 / 3
#eval 12 / 3
#eval 7 - 6
#eval 7 - 7
#eval 7 - 8

/- When using subtraction and division, it is better to do the calculation in the rationals or reals.
We write `(... : ℚ)` to tell Lean that the `...` should be interpreted as a rational number.
Natural numbers will be
*coerce* the value to the rationals.
In the infoview (right half of your screen), these coercions are denoted with `↑`.
-/

section
#eval (12 : ℚ) / 15
#eval (7 : ℤ) - 8
variable (n : ℕ)
#check (n : ℚ)
#check (n + 1 : ℚ)
#check ((n + 1 : ℕ) : ℚ)
#check ((n + 1 : ℤ) : ℚ)
#check ((n - 3) / 2 : ℝ)
end

/-
Some tactics that are useful when working with coercions:
* `norm_cast`: pull coercions out of an expression.
  E.g. turn `↑n * ↑m + ↑k` into `↑(n * m + k)`
* `push_cast`: push coercions into an expression.
  E.g. turn `↑(n * m + k)` into `↑n * ↑m + ↑k`

Note: when coercing from `ℕ` to e.g. `ℚ` these tactics will not push/pull casts along `-` or `/`,
since `↑n - ↑m = ↑(n - m)` and `↑n / ↑m = ↑(n / m)` are not always true.
-/

example (n : ℕ) : ((n + 1 : ℤ) : ℚ) = n + 1 := by norm_cast

example (n m : ℕ) (h : (n : ℚ) + 1 ≤ m) : (n : ℝ) + 1 ≤ m := by {
  sorry
  }

example (n m : ℕ) (h : n = m * m + 2) : (n : ℝ) - 3 = (m + 1) * (m - 1) := by {
  sorry
  }


/- # Recursion and induction

Let's start by defining our own factorial function.
Note that there is no `:=` -/

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

-- illegal:
-- def wrong : ℕ → ℕ
--   | 0 => 1
--   | (n + 1) => wrong (n + 2)






lemma fac_zero : fac 0 = 1 := rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := rfl

example : fac 4 = 24 := rfl

#eval fac 100

theorem fac_pos (n : ℕ) : 0 < fac n := by {
  sorry
  }

open BigOperators Finset

/- We can use `∑ i in range (n + 1), f i` to take the sum `f 0 + f 1 + ⋯ + f n`. -/

example (f : ℕ → ℝ) : ∑ i in range 0, f i = 0 :=
  sum_range_zero f

example (f : ℕ → ℝ) (n : ℕ) : ∑ i in range (n + 1), f i = (∑ i in range n, f i) + f n :=
  sum_range_succ f n

/- Here `range n` or `Finset.range n` is the set `{0, ..., n - 1}`.
It's type is `Finset ℕ`, which is a set
-/
#check Finset.range

/- The following result is denoted using division of natural numbers.
This is defined as division, rounded down.
This makes it harder to prove things about it, so we generally avoid using it
(unless you actually want to round down sometimes). -/


example (n : ℕ) : ∑ i in range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by {
  sorry
  }

/- Some other useful induction principles -/
#check Nat.le_induction
#check Nat.twoStepInduction
#check Nat.strongRec

/- We can use other induction principles with `induction ... using ... with` -/

theorem fac_dvd_fac (n m : ℕ) (h : n ≤ m) : fac n ∣ fac m := by {
  sorry
  }




/-
# Structures and classes

Structures are used to build data and properties together.
For example in the structure below `Point` bundles three coordinates together.
-/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point




section

/- Given a point, we get access to its coordinates / projections. -/
variable (a : Point)
#check a.x
#check a.y
#check a.z
#check Point.x a

example : a.x = Point.x a := rfl

end





/- We can prove that two points are equal using the `ext` tactic. -/

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  ext
  all_goals assumption

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  ext <;> assumption

#check Point.ext
#check Point.ext_iff

/- There are multiple ways to define a point (or more generally an instance of a structure).

Tip: if you write `_` for a Point, a lightbulb 💡 will appear.
Clicking it will give you the skeleton to write all fields. -/

def myPoint1 : Point where
  x := 1
  y := 2
  z := 3

def myPoint2 :=
  { x := 1, y := 2, z := 3 : Point }

def myPoint3 : Point :=
 id {
   x := 1
   y := 2
   z := 3
 }

def myPoint4 : Point := ⟨1, 2, 3⟩

def myPoint5 := Point.mk 1 2 3



namespace Point

/- We can define operations on points, like addition. -/

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

def add' : Point → Point → Point :=
  fun ⟨ux, uy, uz⟩ ⟨vx, vy, vz⟩ ↦ ⟨ux + vx, uy + vy, uz + vz⟩

def add'' : Point → Point → Point
  | ⟨ux, uy, uz⟩, ⟨vx, vy, vz⟩ => ⟨ux + vx, uy + vy, uz + vz⟩

/- We define these operations in `namespace Point`.
This means that if this namespace is open we can write `add p q`.
If the namespace isn't open, we have to write `Point.add p q`.

In either case, we can use the *projection notation*,
`p.add q` where `p q : Point`.
Lean knows that we mean the function `Point.add`,
by looking at the type of `p`, which is `Point`. -/

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

/- You can *open* a namespace to shorten the names in it. -/
open Point

#check add myPoint1 myPoint2











namespace Point

/- We can prove properties about points. `protected` in the line below means that
even in the namespace `Point` we still have to write `Point.add_comm`
(the name is not shortened) -/

protected lemma add_comm (a b : Point) :
  add a b = add b a := by simp [add, add_comm]

#check Point.add_comm

/- We can also state that we want to use the `+` notation here.
In that case, we have to write lemmas stating how `+` computes. -/

instance : Add Point := ⟨add⟩

@[simp] lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp] lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp] lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

example (a b : Point) : a + b = b + a := by {
  sorry
  }

end Point





/- We can bundle properties in structures -/

structure PosPoint where
  x : ℝ
  y : ℝ
  z : ℝ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

def PointPoint.add (a b : PosPoint) : PosPoint :=
{ x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z
  x_pos := by apply add_pos; exact a.x_pos; exact b.x_pos
  y_pos := by linarith [a.y_pos, b.y_pos]
  z_pos := by linarith [a.z_pos, b.z_pos] }

/- Going from `Point` to `PosPoint` has code duplication.
We don't want this when defining monoids, groups, rings, fields. -/

structure PosPoint' extends Point where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

#check PosPoint'.toPoint

def PointPoint'.add (a b : PosPoint') : PosPoint' :=
{ a.toPoint + b.toPoint with
  x_pos := by dsimp; linarith [a.x_pos, b.x_pos]
  y_pos := by dsimp; linarith [a.y_pos, b.y_pos]
  z_pos := by dsimp; linarith [a.z_pos, b.z_pos] }

/- We could also define a type like this using a subtype. It's notation is very similar to sets,
but written as `{x : α // p x}` instead of `{x : α | p x}`. -/

def PosReal : Type :=
  { x : ℝ // x > 0 }

def set_of_positive_reals : Set ℝ :=
  { x : ℝ | x > 0 }

/- However, that doesn't give you nice projections names (automatically).
And it gets ugly when you have more than 2 projections. -/

example (x : PosReal) : x.1 > 0 := x.2

def PosPoint'' : Type :=
  { x : ℝ × (ℝ × ℝ) // x.1 > 0 ∧ x.2.1 > 0 ∧ x.2.2 > 0 }





/- Structures can have parameters -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

#check Triple.mk 1 2 3

#check Triple.mk cos sin tan







/- # Equiv

An important structure is equivalences between two types,
i.e. a bijection (with a chosen inverse).
This exists in the library as `Equiv α β` or `α ≃ β`.  -/

#check Equiv

example {α β : Type*} (e : α ≃ β) (x : α) : β := e.toFun x
example {α β : Type*} (e : α ≃ β) (x : α) : β := e x

example {α β : Type*} (e : α ≃ β) : β ≃ α := e.symm
example {α β : Type*} (e : α ≃ β) (y : β) : α := e.symm y





/- # Abelian groups
Let's define abelians group in Lean. -/

structure AbelianGroup where
  G : Type*
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg (x : G) : G
  add_neg : ∀ x : G, add x (neg x) = zero

def IntGroup : AbelianGroup where
  G := ℤ
  add a b := a + b
  comm := add_comm
  assoc := add_assoc
  zero := 0
  add_zero := by simp
  neg a := -a
  add_neg := Int.add_right_neg

lemma AbelianGroup.zero_add (g : AbelianGroup) (x : g.G) :
    g.add g.zero x = x := by
  rw [g.comm, g.add_zero]




/-
Issues with this approach:
* we want a notation for `AbelianGroup.add` and `AbelianGroup.neg`.
* we want this to be automatically attached to certain concrete type such as `ℕ`, `ℝ`...
* we want that Lean knows that `G × G'` is an abelian group if `G` and `G'` are.

Using `class` instead of `structure` tells Lean to
create a database of "instances of this class".
The `instance` command allows to add entries to this database.
-/


class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

instance : AbelianGroup' ℤ where
  add := fun a b ↦ a + b
  comm := add_comm
  assoc := add_assoc
  zero := 0
  add_zero := by simp
  neg := fun a ↦ -a
  add_neg := by exact?

#eval AbelianGroup'.add (2 : ℤ) 5

infixl:70 " +' " => AbelianGroup'.add

#eval (-2) +' 5

notation " 𝟘 " => AbelianGroup'.zero

prefix:max "-'" => AbelianGroup'.neg

/- When you assume you have an object in a certain class, you put them in square brackets
(and giving a name to them is optional).
Such arguments are called instance-implicit arguments,
Lean will provide them automatically by searching the corresponding database.
-/

#check AbelianGroup'.add

instance AbelianGroup'.prod (G G' : Type*) [AbelianGroup' G] [AbelianGroup' G'] :
    AbelianGroup' (G × G') where
  add a b := (a.1 +' b.1, a.2 +' b.2)
  comm a b := by ext <;> apply AbelianGroup'.comm
  assoc a b c := by ext <;> apply AbelianGroup'.assoc
  zero := (𝟘, 𝟘)
  add_zero a := by ext <;> apply AbelianGroup'.add_zero
  neg a := (-' a.1, -' a.2)
  add_neg a := by ext <;> apply AbelianGroup'.add_neg

/- Now Lean will figure out itself that `AbelianGroup' (ℤ × ℤ)`. -/
set_option trace.Meta.synthInstance true in
#check ((2, 3) : ℤ × ℤ) +' (4, 5)
