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

section ExtraLemmas

lemma pow_self_ne_zero (n : ℕ) : n ^ n ≠ 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · positivity

open Real

attribute [simp] div_left_inj' neg_eq_self self_eq_neg sqrt_eq_zero'

end ExtraLemmas
