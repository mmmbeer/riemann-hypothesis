import Lean

open Lean Elab in
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let opts := ((((Options.empty.set `autoImplicit false).set `relaxedAutoImplicit false).set
    `maxSynthPendingDepth (3 : Nat)).set `maxHeartbeats (4000000 : Nat)).set `Elab.async false
  let mut lastHeader := ""
  let mut base ← mkEmptyEnvironment
  for row in (← IO.FS.readFile args.head!).splitOn "\n" do
    if row.isEmpty then continue
    let [mod, file] := row.splitOn "\t" | throw <| IO.userError row
    let src ← IO.FS.readFile file
    let ctx := Parser.mkInputContext src file
    let (header, ps, messages) ← Parser.parseHeader ctx
    let key := reprStr header.raw.reprint
    if key != lastHeader then
      let (env, msgs) ← processHeader header opts messages ctx
      if msgs.hasErrors then
        for msg in msgs.toList do IO.eprintln (← msg.toString)
        throw <| IO.userError "failed imports"
      base := env
      lastHeader := key
    let s ← Elab.IO.processCommands ctx ps (Command.mkState (base.setMainModule mod.toName) messages opts)
    if s.commandState.messages.hasErrors then
      for msg in s.commandState.messages.toList do
        if msg.severity == .error then IO.println (← msg.toString)
    IO.println s!"@@MODULE {mod} {if s.commandState.messages.hasErrors then "FAIL" else "PASS"}"
    (← IO.getStdout).flush
