import Env
open Lean Elab Command Meta in
elab "#compact_value " n:ident : command => liftTermElabM do
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let some e := (← getConstInfo name).value? | throwError "no value"
  let opts := fun (o : Options) =>
    (((o.set `pp.maxSteps (500000 : Nat)).set `pp.funBinderTypes true).set `pp.proofs true).set `pp.deepTerms true
  let st ← withOptions opts <| PrettyPrinter.delab e
  let fmt ← PrettyPrinter.ppTerm ⟨st⟩
  IO.println ("@@VALUE " ++ n.getId.toString ++ "\n" ++ fmt.pretty 92 ++ "\n@@END")
