import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open BigOperators Function Set Filter Topology TopologicalSpace MeasureTheory
noncomputable section

/- # Today: Topology

We cover chapter 10 from Mathematics in Lean. -/




/- # Limits -/


/-
In topology, one of basic concepts is that of a limit.
Say `f : ℝ → ℝ`. There are many variants of limits.
* the limit of `f(x)` as `x` tends to `x₀`
* the limit of `f(x)` as `x` tends to `∞` or `-∞`
* the limit of `f(x)` as `x` tends to `x₀⁻` or `x₀⁺`
* variations of the above with the additional assumption that `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.
Similarly, the value `f(x)` can have the same behavior:
`f(x)` tends to `∞`, `-∞`, `x₀`, `x₀⁺`, ...

This gives `64` notions of limits.

When we prove that two limits compose: if
`f x` tends to `y₀` when `x` tends to `x₀` and
`g y` tends to `z₀` when `y` tends to `y₀` then
`(g ∘ f) x` tends to `z₀` when `x` tends to `x₀`.
This lemma has 512 variants.

Obviously we don't want to prove this 512 times.
Solution: use filters.










If `X` is a type, a filter `F : Filter X` is a
collection of sets `F.sets : Set (Set X)` satisfying the following:
-/
section Filter

variable {X Y : Type*} (F : Filter X)

#check (F.sets : Set (Set X))
#check (F.univ_sets : univ ∈ F.sets)
#check (F.sets_of_superset : ∀ {U V},
  U ∈ F.sets → U ⊆ V → V ∈ F.sets)
#check (F.inter_sets : ∀ {U V},
  U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets)

end Filter






/-
Examples of filters:
-/

/- `(atTop : Filter ℕ)` is made of sets of `ℕ` containing
`{n | n ≥ N}` for some `N` -/
#check (atTop : Filter ℕ)

example {s : Set ℝ} : s ∈ atTop ↔
  ∃ N, ∀ n ≥ N, n ∈ s := by exact mem_atTop_sets

/- `𝓝 x`, made of neighborhoods of `x` in a topological space -/
#check (𝓝 3 : Filter ℝ)

/- `μ.ae` is made of sets whose complement has zero measure
with respect to a measure `μ`. -/
#check (ae volume : Filter (ℝ × ℝ × ℝ))

/-
It may be useful to think of a filter on a type `X`
as a generalized element of `Set X`.
* `atTop` is the "set of very large numbers"
* `𝓝 x₀` is the "set of points very close to `x₀`."
* For each `s : Set X` we have the so-called *principal filter*
  `𝓟 s` consisting of all sets that contain `s`.
-/


example {s t : Set ℝ} : t ∈ 𝓟 s ↔ s ⊆ t :=
  by exact mem_principal





/- Operations on filters -/

/- the *pushforward* of filters generalizes images of sets. -/
example {X Y : Type*} (f : X → Y) : Filter X → Filter Y :=
  Filter.map f

example {X Y : Type*} (f : X → Y) (F : Filter X) (V : Set Y) :
    V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F := by
  rfl

/- the *pullback* of filters generalizes preimages -/
example {X Y : Type*} (f : X → Y) : Filter Y → Filter X :=
  Filter.comap f

/- These form a *Galois connection* / adjunction -/
example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Filter.map f F ≤ G ↔ F ≤ Filter.comap f G := by
  exact map_le_iff_le_comap

/- `Filter X` has an order that turns it into a complete lattice.
The order is reverse inclusion: -/
example {X : Type*} (F F' : Filter X) :
    F ≤ F' ↔ ∀ V : Set X, V ∈ F' → V ∈ F := by
  rfl

/- This makes the principal filter `𝓟 : Set X → Filter X` monotone. -/
example {X : Type*} : Monotone (𝓟 : Set X → Filter X) := by
  exact monotone_principal

example {X : Type*} {S S' : Set X} (h : S ⊆ S') : 𝓟 S ≤ 𝓟 S' := by
  exact monotone_principal h







/- Using these operations, we can define the limit. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

def Tendsto_iff {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F := by
  rfl

/- A sequence `u` converges to `x` -/
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)

/- `\lim_{x → x₀} f(x) = y₀` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝 x₀) (𝓝 y₀)

/- `\lim_{x → x₀⁻, x ≠ x₀} f(x) = y₀⁺` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝[<] x₀) (𝓝[≥] y₀)

/- Now the following states all possible composition lemmas all at
once! -/
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by {
  rw [Tendsto] at *
  calc
    map (g ∘ f) F = map g (map f F) := rfl
    _ ≤ map g G := by
      --apply map_mono hf
      gcongr
    _ ≤ H := hg

  }

/-
Filters also allow us to reason about things that are
"eventually true". If `F : Filter X` and `P : X → Prop` then
`∀ᶠ n in F, P n` means that `P n` is eventually true for `n` in `F`.
It is defined to be `{ x | P x } ∈ F`.

The following example shows that if `P n` and `Q n` hold for
sufficiently large `n`, then so does `P n ∧ Q n`.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ








section Topology

/- Let's look at the definition of topological space. -/

universe u v
variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]


example {ι : Type*} (s : ι → Set X) :
    interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) := by {
  simp only [subset_iInter_iff]
  intro i x hx
  --rw [mem_interior] at hx ⊢
  apply interior_mono _ hx
  exact iInter_subset_of_subset i fun ⦃a⦄ a ↦ a
  }









/- A map between topological spaces is continuous if the
preimages of open sets are open. -/
example {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

/- It is equivalent to saying that for any `x₀` the function
value `f x` tends to `f x₀` whenever `x` tends to `x₀`. -/
example {f : X → Y} :
    Continuous f ↔ ∀ x₀, Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  exact continuous_iff_continuousAt

/- By definition, the right-hand side states that `f` is
continuous at `x₀`. -/
example {f : X → Y} {x₀ : X} :
    ContinuousAt f x₀ ↔ Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  rfl







/- Neighborhoods are characterized by the following lemma. -/
example {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff

example {x : X} {s : Set X} (h : s ∈ 𝓝 x) : x ∈ s := by
  rw [mem_nhds_iff] at h
  obtain ⟨U, hUs, hUopen, hUx⟩ := h
  exact hUs hUx








/- We can state that a topological space satisfies
separatedness axioms. -/

example : T0Space X ↔ Injective (𝓝 : X → Filter X) := by
  exact t0Space_iff_nhds_injective X

example : T1Space X ↔ ∀ x, IsClosed ({ x } : Set X) :=
  ⟨by exact fun a x ↦ isClosed_singleton, by exact fun a ↦ { t1 := a }⟩

example : T2Space X ↔
    ∀ x y : X, x ≠ y → Disjoint (𝓝 x) (𝓝 y) :=
  t2Space_iff_disjoint_nhds

example : RegularSpace X ↔ ∀ {s : Set X} {a},
    IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a) := by
  exact regularSpace_iff X










/- A set is compact if every open cover has a finite subcover. -/

example {K : Set X} : IsCompact K ↔ ∀ {ι : Type u}
    (U : ι → Set X), (∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i := by
  exact isCompact_iff_finite_subcover

#check CompactSpace

/-
This can also be reformulated using filters.
* `NeBot F` iff `F ≠ ⊥` iff `∅ ∉ F`
* `ClusterPt x F` means that `F` has nontrivial intersection
  with `𝓝 x` (viewed as a generalized sets).
* `K` is compact iff every nontrivial filter that contains `K`
  has a cluster point in `K`.
-/

example (F : Filter X) : NeBot F ↔ F ≠ ⊥ := by
  exact?

example {x : X} (F : Filter X) :
    ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) := by
  rfl

example {K : Set X} : IsCompact K ↔
    ∀ {F} [NeBot F], F ≤ 𝓟 K → ∃ x ∈ K, ClusterPt x F := by
  rfl

end Topology














section Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/- A metric space is a type `X` equipped with a distance function
`dist : X → X → ℝ` with the following properties. -/

#check (dist : X → X → ℝ)
#check (dist_nonneg : ∀ {a b : X}, 0 ≤ dist a b)
#check (dist_eq_zero : ∀ {a b : X}, dist a b = 0 ↔ a = b)
#check (dist_comm : ∀ (a b : X), dist a b = dist b a)
#check (dist_triangle : ∀ (a b c : X), dist a c ≤ dist a b + dist b c)

/- In metric spaces, all topological notions are also
characterized by the distance function. -/

example (f : X → Y) (x₀ : X) : ContinuousAt f x₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ {x},
    dist x x₀ < δ → dist (f x) (f x₀) < ε :=
  Metric.continuousAt_iff

example (x : X) (ε : ℝ) :
    Metric.ball x ε = { y | dist y x < ε } := by
  rfl

example (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

end Metric




/- # Exercises

The goal of these exercise is to prove that
the regular open sets in a topological space form a complete boolean algebra.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/


variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

theorem le_def {U V : RegularOpens X} : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp
@[simp] theorem regular {U : RegularOpens X} : interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X :=
  ⟨closure U, sorry⟩

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/
@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X :=
  ⟨interior C, sorry, sorry⟩

/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by sorry

@[simp] lemma cl_int : U.cl.int = U := by sorry

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi

@[simp] lemma coe_inf {U V : RegularOpens X} : ↑(U ⊓ V) = (U : Set X) ∩ V := by
  have : U ⊓ V = (U.cl ⊓ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_sup {U V : RegularOpens X} : ↑(U ⊔ V) = interior (closure ((U : Set X) ∪ V)) := by
  have : U ⊔ V = (U.cl ⊔ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_top : ((⊤ : RegularOpens X) : Set X) = univ := by
  have : (⊤ : RegularOpens X) = (⊤ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := by
  have : (⊥ : RegularOpens X) = (⊥ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_sInf {U : Set (RegularOpens X)} :
    ((sInf U : RegularOpens X) : Set X) =
    interior (⋂₀ ((fun u : RegularOpens X ↦ closure u) '' U)) := by
  have : sInf U = (sInf (cl '' U)).int := rfl
  simp [this]

@[simp] lemma Closeds.coe_sSup {C : Set (Closeds X)} : ((sSup C : Closeds X) : Set X) =
    closure (⋃₀ ((↑) '' C)) := by
  have : sSup C = Closeds.closure (sSup ((↑) '' C)) := rfl
  simp [this]

@[simp] lemma coe_sSup {U : Set (RegularOpens X)} :
    ((sSup U : RegularOpens X) : Set X) =
    interior (closure (⋃₀ ((fun u : RegularOpens X ↦ closure u) '' U))) := by
  have : sSup U = (sSup (cl '' U)).int := rfl
  simp [this]

/- We still have to prove that this gives a distributive lattice.
Note: these are hard; you might want to do the next exercises first. -/
instance completeDistribLattice : CompleteDistribLattice (RegularOpens X) :=
  CompleteDistribLattice.ofMinimalAxioms
  { completeLattice with
    inf_sSup_le_iSup_inf := by sorry
    iInf_sup_le_sup_sInf := by sorry
    }


instance : HasCompl (RegularOpens X) := sorry


@[simp]
lemma coe_compl (U : RegularOpens X) : ↑Uᶜ = interior (U : Set X)ᶜ := by sorry


instance : CompleteBooleanAlgebra (RegularOpens X) :=
  { inferInstanceAs (CompleteDistribLattice (RegularOpens X)) with
    inf_compl_le_bot := by sorry
    top_le_sup_compl := by sorry
    le_sup_inf := by sorry
    sdiff_eq := by sorry
    himp_eq := by sorry }
