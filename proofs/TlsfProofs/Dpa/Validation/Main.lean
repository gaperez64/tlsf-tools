import TlsfProofs.Dpa.Validation.ProtocolChecks

open Tlsf.Dpa.Validation

def main (args : List String) : IO UInt32 := do
  let err ← IO.getStderr
  match args with
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
