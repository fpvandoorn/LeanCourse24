import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Dvd
noncomputable section
open Function Ideal Polynomial Classical
open scoped Matrix
-- This is removed intentionally and should not be used manually in the exercises
attribute [-ext] LinearMap.prod_ext


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 8.2 and 9.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 26.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by {
  rw [span_gcd, ← span_union, Set.singleton_union]
  }

example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by {
  ext k
  simp [mem_span_singleton, lcm_dvd_iff]
  }

/- Show that transposing a matrix gives rise to a linear equivalence. -/
example {R M m n : Type*} [Ring R] [AddCommGroup M] [Module R M] :
  Matrix m n M ≃ₗ[R] Matrix n m M where
    toFun M := Mᵀ
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    invFun := flip -- i.e. `fun f x y ↦ f y x`
    left_inv := congrFun rfl
    right_inv := congrFun rfl

/- A ring has characteristic `p` if `1 + ⋯ + 1 = 0`, where we add `1` `p` times to itself.
This is written `CharP` in Lean.
In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by
  have : ((2 : ℕ) : R) • m = (0 : R) • m := by rw [CharP.cast_eq_zero R 2]
  simpa [two_smul] using this

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
/- Let's define the Frobenius morphism `x ↦ x ^ p`.
You can use lemmas from the library.
We state that `p` is prime using `Fact p.Prime`.
This allows type-class inference to see that this is true.
You can access the fact that `p` is prime using `hp.out`. -/

def frobeniusMorphism : R →+* R :=
  { toFun := fun x ↦ x^p
    map_one' := by simp
    map_mul' := fun x y ↦ mul_pow x y p
    map_zero' := by simp [hp.out.ne_zero]
    map_add' := add_pow_char R
  }

@[simp] lemma frobeniusMorphism_def (x : R) : frobeniusMorphism p R x = x ^ p := rfl

/- Prove the following equality for iterating the frobenius morphism. -/
lemma iterate_frobeniusMorphism (n : ℕ) (x : R) : (frobeniusMorphism p R)^[n] x = x ^ p ^ n := by {
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', pow_succ', pow_mul', Function.comp_apply,
      frobeniusMorphism_def, ih]
  }

/- Show that the Frobenius morphism is injective on a domain. -/
lemma frobeniusMorphism_injective [IsDomain R] :
    Function.Injective (frobeniusMorphism p R) := by {
  have : ∀ x : R, x ^ p = 0 → x = 0 := fun x ↦ pow_eq_zero
  intro x y h
  rw [← sub_eq_zero, ← (frobeniusMorphism p R).map_sub, frobeniusMorphism_def] at h
  specialize this _ h
  rwa [sub_eq_zero] at this
  }

/- Show that the Frobenius morphism is bijective on a finite domain. -/
lemma frobeniusMorphism_bijective [IsDomain R] [Finite R] :
    Function.Bijective (frobeniusMorphism p R) := by {
  have := frobeniusMorphism_injective p R
  exact Finite.injective_iff_bijective.mp this
  }

example [IsDomain R] [Finite R] (k : ℕ) (x : R) : x ^ p ^ k = 1 ↔ x = 1 := by {
  rw [← iterate_frobeniusMorphism]
  convert ((frobeniusMorphism_injective p R).iterate k).eq_iff
  rw [iterate_map_one]
  }

example {R : Type*} [CommRing R] [IsDomain R] [Finite R] [CharP R 2] (x : R) : IsSquare x := by {
  use invFun (frobeniusMorphism 2 R) x
  nth_rw 1 [← rightInverse_invFun (frobeniusMorphism_bijective 2 R).surjective x]
  simp [pow_two]
  }

end Frobenius


section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
prove that the units of a ring form a group.
Hint: I recommend that you first prove that the product of two units is again a unit,
and that you define the inverse of a unit separately using `Exists.choose`.
Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
(`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

def IsAUnit.mul {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  use y' * x'
  rw [mul_assoc, ← mul_assoc x', hx', one_mul, hy']

instance groupUnits : Group {x : R // IsAUnit x} where
  mul := fun x y ↦ ⟨x.1 * y.1, x.2.mul y.2⟩
  mul_assoc := by intros; ext; apply mul_assoc
  one := ⟨1, ⟨1, one_mul 1⟩⟩
  one_mul := by intros; ext; apply one_mul
  mul_one := by intros; ext; apply mul_one
  inv := fun x ↦ ⟨x.2.choose, ⟨x, by rw [mul_comm]; exact x.2.choose_spec⟩⟩
  inv_mul_cancel := by intro x; ext; exact x.2.choose_spec

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := rfl

end Ring

/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).-/
#check exists_ne
lemma commutative_of_module {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by {
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have h2 (f : M →ₗ[R] M) : (r * s) • f = (s * r) • f
  · ext x
    rw [h, mul_smul, ← f.map_smul, ← h, (r • f).map_smul]
    simp_rw [h, mul_smul]
  specialize h2 LinearMap.id
  apply_fun (· x) at h2
  simp [h] at h2
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at h2
  simpa [hx] using h2
  }


/-! # Exercises to hand-in. -/

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R] [CharP R p] in
open Nat Finset in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by {
  have hp' : p.Prime := hp.out
  -- `Finset.Ioo a b` is the finite set `{n | a < n < b }`.
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [hp'.pos]
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i hi
    simp at hi
    apply hp'.dvd_choose_self hi.1.ne' hi.2
  have middle_sum_eq_zero : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
    calc
      _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by
        apply sum_congr rfl
        intro i hi
        simp [CharP.cast_eq_zero_iff R p, dvd_choose i hi]
      _ = 0 := by simp
  simp [add_pow, Finset.sum_range_succ, range_eq_insert_Ioo, sum_insert, middle_sum_eq_zero,
    add_comm]
  }


section LinearMap

variable {R M₁ M₂ N M' : Type*} [CommRing R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup M']
  [Module R M₁] [Module R M₂] [Module R N] [Module R M']

/- Define the coproduct of two linear maps, and prove the characterization below.
Note that this proof works exactly the same for vector spaces over a field as it works
for modules over a ring, so feel free to think of `M₁`, `M₂`, `N` and `M'` as vector spaces.
You might recognize this as the characterization of a *coproduct* in category theory. -/

def coproduct (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x := f x.1 + g x.2
  map_add' x y := by simp; abel
  map_smul' r x := by simp

-- this can be useful to have as a simp-lemma, and should be proven by `rfl`
@[simp] lemma coproduct_def (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  coproduct f g (x, y) = f x + g y := rfl

lemma coproduct_unique {f : M₁ →ₗ[R] N} {g : M₂ →ₗ[R] N} {l : M₁ × M₂ →ₗ[R] N} :
    l = coproduct f g ↔
    l.comp (LinearMap.inl R M₁ M₂) = f ∧
    l.comp (LinearMap.inr R M₁ M₂) = g := by {
  constructor
  · intro h
    subst h
    constructor
    · ext
      simp
    · ext
      simp
  · intro ⟨h1, h2⟩
    ext ⟨m₁, m₂⟩
    rw [LinearMap.ext_iff] at h1 h2
    simp at *
    rw [← h1, ← h2, ← l.map_add]
    simp
  }


end LinearMap
