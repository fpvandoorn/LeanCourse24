import Mathlib.Tactic
import Mathlib.Topology.Instances.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Topology Filter Set Function TopologicalSpace
open MeasureTheory
set_option linter.unusedVariables false

namespace TopologySession











/-
In topology, one of basic concepts is that of a limit.
Say `f : ℝ → ℝ`. There are many variants of limits.
* the limit of `f(x)` as `x` tends to `x₀`
* the limit of `f(x)` as `x` tends to `∞` or `-∞`
* the limit of `f(x)` as `x` tends to `x₀⁻` or `x₀⁺`
* variations of the above with the additional assumption that `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.
Similarly, the value `f(x)` can have the same behavior: `f(x)` tends to `∞`, `-∞`, `x₀`, `x₀⁺`, ...

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

variable {X Y : Type _} (F : Filter X)

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

/- `𝓝 x`, made of neighborhoods of `x` in a topological space -/
#check (𝓝 3 : Filter ℝ)

/- `μ.ae` is made of sets whose complement has zero measure with respect to a measure `μ`. -/
#check (volume.ae : Filter (ℝ × ℝ × ℝ))

/-
It may be useful to think of a filter on a type `X`
as a generalized element of `Set X`.
* `atTop` is the "set of very large numbers"
* `𝓝 x₀` is the "set of points very close to `x₀`."
* For each `s : Set X` we have the so-called *principal filter*
  `𝓟 s` consisting of all sets that contain `s` (exercise!).
-/






/- Operations on filters -/

/- the *pushforward* of filters -/
example (f : X → Y) : Filter X → Filter Y :=
  Filter.map f

example (f : X → Y) (F : Filter X) (V : Set Y) :
    V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F := by
  rfl

/- the *pullback* of filters generalizes -/
example (f : X → Y) : Filter Y → Filter X :=
  Filter.comap f

/- These form a *Galois connection* / adjunction -/
example (f : X → Y) (F : Filter X) (G : Filter Y) :
    Filter.map f F ≤ G ↔ F ≤ Filter.comap f G := by
  exact?

/- `Filter X` has an order that turns it into a complete lattice. The order is reverse inclusion: -/
example (F F' : Filter X) :
    F ≤ F' ↔ ∀ V : Set X, V ∈ F' → V ∈ F := by
  rfl

/- This makes the principal filter `𝓟 : Set X → Filter X` monotone. -/
example : Monotone (𝓟 : Set X → Filter X) := by
  exact?







/- Using these operations, we can define the limit. -/
def Tendsto {X Y : Type _} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

def Tendsto_iff {X Y : Type _} (f : X → Y)
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
once!-/
example {X Y Z : Type _} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H :=
  sorry -- exercise!



/-
Filters also allow us to reason about things that are
"eventually true". If `F : Filter X` and `P : X → Prop` then
`∀ᶠ n in F, P n` means that `P n` is eventually true for `n` in `F`. It is defined to be `{ x | P x } ∈ F`.

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

variable {X : Type _} [TopologicalSpace X]
variable {Y : Type _} [TopologicalSpace Y]

/- A map between topological spaces is continuous if the
preimages of open sets are open. -/
example {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

/- It is equivalent to saying that for any `x₀` the function
value `f x` tends to `f x₀` whenever `x` tends to `x₀`. -/
example {f : X → Y} :
    Continuous f ↔ ∀ x₀, Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  exact?

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
  rcases h with ⟨t, hts, ht, hxt⟩
  exact hts hxt








/- We can state that a topological space satisfies
  separatedness axioms. -/

example : T0Space X ↔ Injective (𝓝 : X → Filter X) := by
  exact?

example : T1Space X ↔ ∀ x, IsClosed ({ x } : Set X) :=
  ⟨by exact?, by exact?⟩

example : T2Space X ↔
    ∀ x y : X, x ≠ y → Disjoint (𝓝 x) (𝓝 y) := by
  exact?

example : RegularSpace X ↔ ∀ {s : Set X} {a},
    IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a) := by
  exact?










/- A set is compact if every open cover has a finite subcover. -/

example {K : Set X} : IsCompact K ↔ ∀ {ι : Type _}
    (U : ι → Set X), (∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i := by
  exact?

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

example (F : Filter X) :
    ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) := by
  rfl

example {K : Set X} : IsCompact K ↔
    ∀ {F} [NeBot F], F ≤ 𝓟 K → ∃ x ∈ K, ClusterPt x F := by
  rfl

end Topology














section Metric

variable {X Y : Type _} [MetricSpace X] [MetricSpace Y]

/- A metric space is a type `X` equipped with a distance function `dist : X → X → ℝ` with the following properties. -/

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

end TopologySession