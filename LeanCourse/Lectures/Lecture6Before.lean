import LeanCourse.Common
open Real Function Set
noncomputable section





/-
# Practical remarks
* Assignment 6 will be posted tonight. It is due on 19.11. Upload it to eCampus.

* Start thinking about a formalization projects.
  This Friday we will talk about how to get started,
  and will give some possible formalization project topics.

* Over the next couple of classes we'll cover some topics in undergraduate mathematics, and see
  how this is done in Lean.
  - Group theory: group homomorphisms, subgroups, quotient groups, group actions
  - Ring theory: ideals, units, polynomials
  - Linear algebra: linear maps, subspaces, endomorphisms, matrices, bases
  - Topology: Topological spaces, metric spaces, Hausdorff spaces, compact sets
  - Calculus: total derivative of a multivariate function
  - Integration: measures
-/

/- # Last Week -/

/-
Last time we discussed numbers and structures:
* The tactics `norm_num`, `omega`, `positivity`,
  `field_simp`, `norm_cast` and `push_cast`.
* Recursion and induction
* How to define and work with structures and classes
-/


/- # A note on universes

Lean has a hierarchy of universes. -/

#check ℝ
#check Type 0
#check Type 1
#check Type 2

/- You can also work in a variable universe. -/

universe u v
#check Type u
#check Type (v + 3)
#check Type (max u v)
#check fun (α : Type u) (β : Type v) ↦ α → β
-- #check Type (u + v) -- the operations on universes are very limited.

/-
* `Type*` means `Type u` for a *variable* `u`
* `Type _` means an arbitary universe (variable or not)

In Mathlib, when introducing a new type `α`,
we generally write `(α : Type*)` to be as general as possible.
-/

#check Type*
#check Type _


example : Type (u + 3) = Type _ := by rfl
-- example : Type (u + 3) = Type* := by rfl -- error

/-
* `Prop` is a bottom universe below `Type`.
* `Sort` is used to write "`Prop` or `Type`"
-/

#check Prop
#check Sort 0
#check Sort 1
#check Sort 2
#check Sort (u + 1)
#check Sort*


/- ## A note on coercions

You can specify *coercions* to say that an element of one type
can be silently coerced to an element of another type.
We've already seen the coercions
`ℕ → ℤ → ℚ → ℝ → ℂ`
for numbers.
-/

#check fun n : ℕ ↦ (n : ℚ)

abbrev PosReal : Type := {x : ℝ // x > 0}

instance : Coe PosReal Real := ⟨fun x ↦ x.1⟩

def diff (x y : PosReal) : ℝ := x - y

/- coercions can be composed. -/
#check fun (x : PosReal) ↦ (x : ℂ)




/-
* We use `CoeSort` to coerce to `Type _` (or `Sort _`)
* We use `CoeFun` to coerce to functions.
-/
structure PointedType where
  carrier : Type*
  pt : carrier

instance : CoeSort PointedType Type* := ⟨fun α ↦ α.carrier⟩

structure PointedFunction (X Y : PointedType) where
  toFun : X → Y
  toFun_pt : toFun X.pt = Y.pt

infix:50 " →. " => PointedFunction

instance {X Y : PointedType} : CoeFun (X →. Y) (fun _ ↦ X → Y) := ⟨fun e ↦ e.toFun⟩

-- this tells the pretty printer to print the operation with `↑`.
attribute [coe] PointedFunction.toFun

namespace PointedFunction

variable {X Y Z : PointedType}

@[simp] lemma coe_pt (f : X →. Y) : f X.pt = Y.pt := f.toFun_pt

def comp (g : Y →. Z) (f : X →. Y) : X →. Z :=
{ toFun := g ∘ f
  toFun_pt := by simp }

end PointedFunction




/- ## A note on subtypes

As mentioned last week, you can define subtypes of a given type.
-/

#check {x : ℝ // 2 ≤ x }

/- You can also treat a set `s` as the subtype `{x // x ∈ s}`.
This operation is a coercion. -/
section
variable (s : Set ℝ)
#check (s : Type)

example (s : Set ℝ) (x : s) : (x : ℝ) ∈ s := x.2
end

/- However, subtypes are often not that convenient to work with,
and generally it's easier to reformulate a statement without using subtypes. -/


/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := sorry

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := sorry

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := sorry

/- Only specify that a function is well-behaved
on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := sorry





/- # Additive vs Multiplicative classes. -/

/- In Mathlib, there are two notions of abelian groups,
one written using `(*, 1, ⁻¹)` and one using `(+, 0, -)`. -/

#check CommGroup
#check AddCommGroup


/- To explain this distinction, consider monoids
(sets/types with a binary operation and a unit for the operation).
`(ℝ, +, 0)` and `(ℝ, *, 1)` are both monoids,
and we want to have a distinction in notation and
lemma names of these two structures. -/

#check Monoid
#check AddMonoid

example : CommMonoid ℝ := by infer_instance
example : AddCommMonoid ℝ := by infer_instance
example (x : ℝ) : x + 0 = x := add_zero x
example (x : ℝ) : x * 1 = x := mul_one x

/- In Mathlib there is a `@[to_additive]` command
that automatically translates a lemma written
multiplicatively to a lemma written additively. -/




/- # Monoids

The type of monoids structures on a type `M` with multiplicative notation is `Monoid M`.

The additive notation version is `AddMonoid`.
The commutative versions add the `Comm` prefix before `Monoid`. -/

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

/- Note in particular that `AddMonoid` exists, although it would be very confusing to use
additive notation in a non-commutative case on paper. -/





/- The type of morphisms between monoids `M` and `N`
is called `MonoidHom M N` and denoted by `M →* N`.
The additive version is called `AddMonoidHom` and denoted by `M →+ N`.

They both have a coercion to functions. -/

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) :
    f (x * y) = f x * f y := by exact?

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero



/- Those morphisms are bundled maps,
i.e. they package together a map and some properties of this map.
Chapter 7 of MiL contain a lot more explanations about that.
Here we simply note the unfortunate consequence
that we cannot use ordinary function composition.
We need to use `MonoidHom.comp` and `AddMonoidHom.comp`. -/

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f






/- # Groups and their morphisms -/

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

/- Similar to the `ring` tactic that we saw earlier,
there is a `group` tactic that proves every identity
which follows from the group axioms
without using additional assumptions.
(hence one can see it as a tactic that
proves identities that hold in a free group). -/

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x*z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

/- And there is similar a tactic for identities
in commutative additive groups called `abel`. -/

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

/-
Groups morphisms are exactly monoid morphisms between groups
-/

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) :
    f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) :
    f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

/- Note that a map between group that preserves `*`
is automatically a group homomorphism. -/
example {G H : Type*} [Group G] [Group H] (f : G → H)
    (h : ∀ x y, f (x * y) = f x * f y) : G →* H :=
  MonoidHom.mk' f h

/-
There is also a type `MulEquiv` of group (or monoid)
isomorphisms denoted by `≃*`
(and `AddEquiv` denoted by `≃+` in additive notation).
It works similar to `Equiv`.
The inverse of `f : G ≃* H` is `f.symm : H ≃* G`,
composition is `MulEquiv.trans` and
the identity isomorphism of `G` is `MulEquiv.refl G`.
This type is automatically coerced to morphisms and functions.
-/

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G := by exact?






/-
# Subgroups

In the same way group morphisms are bundled,
subgroups are also bundles made of a set in `G`
and some closure properties.
-/


example {G : Type*} [Group G] (H : Subgroup G) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) : 1 ∈ H :=
  H.one_mem

example {G : Type*} [Group G] (H : Subgroup G) {x : G}
    (hx : x ∈ H) : x⁻¹ ∈ H :=
  H.inv_mem hx

/-
In the above example, it is important to understand that
`Subgroup G` is the type of subgroups of `G`.
It is not a predicate on `Set G`.
It is endowed with a coercion to `Set G`
and a membership predicate on `G`.
See Chapter 7 of MiL for explanations
about why and how things are set up like this.

Of course the type class instance system knows
that a subgroup of a group inherits a group structure.
-/

example {G : Type*} [Group G] (H : Subgroup G) :
    Group H := by infer_instance

/-
Here `H` is coerced to the subtype `{x : G // x ∈ H}`,
just like a set.
-/

example {G : Type*} [Group G] (H : Subgroup G) :
    Group {x : G // x ∈ H} := by infer_instance

/-
An important benefit of having a type `Subgroup G`
instead of a predicate `IsSubgroup : Set G → Prop`
is that one can easily endow it with additional structure.
Crucially this includes a complete lattice structure
with respect to inclusion (denoted `≤` in Lean).
For instance, instead of having a lemma stating that an intersection
of two subgroups of `G`, we have the lattice operation `⊓`
and all lemmas about lattices are readily available.
-/

example {G : Type*} [Group G] : CompleteLattice (Subgroup G) := by
  infer_instance

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := by rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    H ⊓ H' ≤ H := inf_le_left

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) =
    Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  simp [Subgroup.closure_union]

/-
Another subtlety is `G` itself does not have type `Subgroup G`,
so we need a way to talk about `G` seen as a subgroup of `G`.
This is also provided by the lattice structure.
We are talking about the top element of this lattice.
-/

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := by
  trivial

/-
Similarly the bottom element of this lattice is the subgroup
whose only element is `1`.
-/

example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 :=
  Subgroup.mem_bot



/- One can pushforward (image) and pullback (preimage)
of subgroups with respect to a morphism. -/

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G)
    (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H)
    (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'



/- Two important subgroups are the kernel and the range of a homomorphism. -/

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range





/- # Quotient groups -/

/-
The quotient of a group `H` by a normal subgroup `H` is denoted `G ⧸ H`.
If `H` is not normal, this stands for the left cosets of `H`.

-/

section QuotientGroup

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] :
    Group (G ⧸ H) := by infer_instance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] :
    G →* G ⧸ H :=
  QuotientGroup.mk' H

/- The universal property of quotient groups -/
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h

/- The first isomorphism theorem -/
example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ ≃* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G'⧸ N':=
  QuotientGroup.map N N' φ h

end QuotientGroup
