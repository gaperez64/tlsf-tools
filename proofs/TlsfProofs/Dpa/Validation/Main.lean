import TlsfProofs.Dpa.Validation.ProtocolChecks

open Tlsf.Dpa.Validation

private def profile (input output : String) : IO UInt32 := do
  let out ← IO.getStdout
  let start ← IO.monoMsNow
  let .ok r := parseRequest input | return 1
  let .ok d := parseDump r output | return 1
  out.putStrLn s!"parsed: {(← IO.monoMsNow) - start} ms"
  out.flush
  let rank := fun _ : Tlsf.Formula (Fin r.names.size) => 0
  let f := Tlsf.Dpa.Impl.normalize r.source
  out.putStrLn s!"normalized ({f.atoms.length} atoms): {(← IO.monoMsNow) - start} ms"
  out.flush
  let admission := Tlsf.Dpa.Impl.transportedResearchCheck rank f
  out.putStrLn s!"admission {admission}: {(← IO.monoMsNow) - start} ms"
  out.flush
  let some reference := Tlsf.Dpa.Impl.construct rank rank f | return 1
  out.putStrLn s!"constructed ({reference.store.length} components): {(← IO.monoMsNow) - start} ms"
  out.flush
  let some table := reference.exportParity 10000 | return 1
  out.putStrLn s!"exported ({table.states.size} states): {(← IO.monoMsNow) - start} ms"
  out.flush
  let cached := freeze (table.parity reference.finiteParitySource reference.paritySame)
  let priorities := cached.rows.toArray.foldl (fun n row =>
    n + row.toArray.foldl (fun n e => n + e.2) 0) 0
  out.putStrLn s!"frozen ({priorities} priority sum): {(← IO.monoMsNow) - start} ms"
  out.flush
  let result := checkCompact d.parity cached.machine
  out.putStrLn s!"checked {result}: {(← IO.monoMsNow) - start} ms"
  out.flush
  pure (if result then 0 else 1)

def main (args : List String) : IO UInt32 := do
  let err ← IO.getStderr
  match args with
  | ["--profile", request, dump] => profile (← IO.FS.readFile request) (← IO.FS.readFile dump)
  | ["--self-test"] =>
    let mut failures := 0
    for (name, ok) in protocolChecks do
      unless ok do
        failures := failures + 1
        err.putStrLn s!"FAIL {name}"
    (← IO.getStdout).putStrLn s!"{protocolChecks.length} protocol checks, {failures} failures"
    pure (if failures == 0 then 0 else 1)
  | [request, dump] =>
    try
      let input ← IO.FS.readFile request
      let output ← IO.FS.readFile dump
      match do
        let r ← parseRequest input
        let d ← parseDump r output
        validate r d 10000
      with
      | .ok () => (← IO.getStdout).putStrLn "pass"; pure 0
      | .error reason => err.putStrLn s!"FAIL {reason}"; pure 1
    catch e => err.putStrLn s!"FAIL {e}"; pure 1
  | _ => err.putStrLn "usage: dpaValidate REQUEST DUMP"; pure 2
