import Lean

open Lean Elab Command Meta in
elab "#compare_with_archive " n:ident path:str val:num : command => liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let (data, _) ← readModuleData path.getString
  let some old := data.constants.find? (·.name == name) | throwError "missing compiled declaration {n}"
  let new ← getConstInfo name
  unless old.levelParams == new.levelParams do throwError "universe parameters changed for {n}"
  unless ← isDefEq old.type new.type do throwError "type changed for {n}"
  let rec checkNames (a b : Expr) : MetaM Unit := do
    match a, b with
    | .forallE x _ u i, .forallE y _ v j =>
      unless i == j && (x == y || (x.hasMacroScopes && y.hasMacroScopes)) do
        throwError "binder changed for {n}: {x} / {y}"
      checkNames u v
    | _, _ => pure ()
  checkNames old.type new.type
  if val.getNat == 1 then
    let some oldValue := old.value? | throwError "original definition has no body"
    let some newValue := new.value? | throwError "changed definition has no body"
    unless ← isDefEq oldValue newValue do throwError "definition changed for {n}"
