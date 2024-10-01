import Mathlib.Tactic

-- don't edit this file!

set_option warningAsError false

section
open Lean Parser Tactic

macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

macro (name := ring_at) "ring" cfg:config ? loc:location : tactic =>
  `(tactic| ring_nf $cfg ? $loc)

end

section delab

section existential
open Lean Parser Term PrettyPrinter Delaborator

/-- Delaborator for existential quantifier, including extended binders. -/
-- TODO: reduce the duplication in this code
@[delab app.Exists]
def exists_delab' : Delab := whenPPOption Lean.getPPNotation do
  let #[ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName $ fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(∃ (_ : $dom), $body)
      else if prop || ppTypes then
        `(∃ ($x:ident : $dom), $body)
      else
        `(∃ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(∃ $i:ident, $j:ident ∈ $s ∧ $body)
    | `(∃ ($i:ident : $_), $j:ident ∈ $s ∧ $body) =>
      if i == j then `(∃ $i:ident ∈ $s, $body) else pure stx
    | `(∃ $x:ident, $y:ident > $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident > $z ∧ $body) =>
      if x == y then `(∃ $x:ident > $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident < $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident < $z ∧ $body) =>
      if x == y then `(∃ $x:ident < $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ≥ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ≥ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ≥ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ≤ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ≤ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ≤ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ∉ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ∉ $z ∧ $body) => do
      if x == y then `(∃ $x:ident ∉ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊆ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊆ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊆ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊂ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊂ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊂ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊇ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊇ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊇ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ⊃ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ⊃ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ⊃ $z, $body) else pure stx
    | _ => pure stx
  match stx with
  | `(∃ $group:bracketedExplicitBinders, ∃ $[$groups:bracketedExplicitBinders]*, $body) =>
    `(∃ $group $groups*, $body)
  | `(∃ $b:binderIdent, ∃ $[$bs:binderIdent]*, $body) => `(∃ $b:binderIdent $[$bs]*, $body)
  | _ => pure stx
end existential

end delab

namespace Nat
open Lean Elab Term Meta

def elabIdentFactorial : TermElab := fun stx expectedType? =>
  match stx with
  | `($name:ident) => do
    let name := name.getId
    if name.hasMacroScopes then
      -- I think this would mean the name appears from within a quote.
      -- I'm not sure how to properly deal with this, and it seems ok to just not.
      throwUnsupportedSyntax
    else
      try
        elabIdent stx expectedType?
      catch e =>
        match name with
        | .str n s =>
          if s.endsWith "!" then
            let name' := Name.str n (s.dropRight 1)
            try
              elabTerm (← `(Nat.factorial $(mkIdent name'))) expectedType?
            catch _ =>
              throw e
          else
            throw e
        | _ => throw e
  | _ => throwUnsupportedSyntax

attribute [scoped term_elab ident] elabIdentFactorial

attribute [eliminator] Nat.recAux

@[elab_as_elim]
def two_step_induction {P : ℕ → Sort*} (zero : P 0) (one : P 1)
    (step : ∀ (k : ℕ), (IH0 : P k) → (IH1 : P (k + 1)) → P (k + 2)) (n : ℕ) :
    P n := by
  induction n using Nat.strongRec with
  | ind n ih =>
    rcases n with _|n
    · exact zero
    rcases n with _|n
    · exact one
    apply step
    · apply ih; linarith
    · apply ih; linarith



end Nat

namespace Filter
variable {α β : Type*} {m : α → β}
@[gcongr]
theorem map_le_map {F G : Filter α} (h : F ≤ G) : map m F ≤ map m G :=
  map_mono h

@[gcongr]
theorem comap_le_comap {F G : Filter β} (h : F ≤ G) : comap m F ≤ comap m G :=
  comap_mono h
end Filter

attribute [gcongr] interior_mono closure_mono

section ExtraLemmas

lemma pow_self_ne_zero (n : ℕ) : n ^ n ≠ 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · positivity

open Real

attribute [simp] div_left_inj' neg_eq_self_iff eq_neg_self_iff sqrt_eq_zero' Int.ModEq.rfl

end ExtraLemmas
