import Lean
open Lean Elab Command Meta

elab "#compact_type " n:ident : command => liftTermElabM do
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let ci ← getConstInfo name
  let opts := fun (o : Options) =>
    (((o.set `pp.maxSteps (500000 : Nat)).set `pp.piBinderNames true).set `pp.proofs true).set `pp.deepTerms true
  let st ← withOptions opts <| PrettyPrinter.delab ci.type
  let fmt ← PrettyPrinter.ppTerm ⟨st⟩
  IO.println ("@@TYPE " ++ n.getId.toString ++ "\n" ++ fmt.pretty 92 ++ "\n@@END")

elab "#same_signature " n:ident " matches " t:term : command => liftTermElabM do
  let ci ← getConstInfo (← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n)
  let old ← Term.elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let old ← instantiateMVars old
  unless ← isDefEq ci.type old do throwError "signature differs for {n}"
  let rec binders (a b : Expr) : MetaM Unit := do
    match a, b with
    | .forallE na _ ba ia, .forallE nb _ bb ib =>
      unless ia == ib && (na == nb || (na.hasMacroScopes && nb.hasMacroScopes)) do
        throwError "binder changed for {n}: {na} vs {nb}, {repr ia} vs {repr ib}"
      binders ba bb
    | _, _ => pure ()
  binders ci.type old
