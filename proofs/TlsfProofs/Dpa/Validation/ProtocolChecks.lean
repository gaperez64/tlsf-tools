import TlsfProofs.Dpa.Validation.Dump
import TlsfProofs.Dpa.Validation.Checks

namespace Tlsf.Dpa.Validation

private def request := "TV1 parity default 1 a G F $a"
private def dump := "TV1 parity default 1 a G F $a states 1 0 0 0 0 2 0 1 0 3 end"

private def probe (input output : String) : Bool :=
  (do
    let r ← parseRequest input
    let d ← parseDump r output
    validate r d 64).isOk

private def dagRequest := "TVD1 parity default 1 0 a positive objective & 1 G F $a " ++
  "normalization caller-trusted dag 5 3 " ++
  "2 4294967295 4294967295 0 " ++
  "10 0 4294967295 4294967295 " ++
  "11 1 4294967295 4294967295 " ++
  "4 2 2 4294967295 " ++
  "1 4294967295 4294967295 4294967295"

private def dagDump := dagRequest ++ " states 1 0 0 0 0 2 0 1 0 3 end"

private def binds (input output : String) : Bool :=
  (do let r ← parseRequest input; let _ ← parseDump r output; pure ()).isOk

private def dagChecks : List (String × Bool) := [
  ("DAG-shared-nonfinal-root", probe dagRequest dagDump),
  ("DAG-entry-point-binding", !binds dagRequest (dagDump.replace "TVD1" "TV1")),
  ("DAG-kind-binding", !binds dagRequest (dagDump.replace "parity" "buchi")),
  ("DAG-admission-binding", !binds dagRequest (dagDump.replace "default" "general")),
  ("DAG-partition-binding", !binds dagRequest (dagDump.replace "1 0 a" "0 1 a")),
  ("DAG-sign-binding", !binds dagRequest (dagDump.replace "positive" "negative")),
  ("DAG-objective-binding", !binds dagRequest (dagDump.replace "& 1 G F" "| 1 G F")),
  ("DAG-premise-required", !(parseRequest (dagRequest.replace "caller-trusted" "proved")).isOk),
  ("DAG-root-binding", !binds dagRequest (dagDump.replace "dag 5 3" "dag 5 2")),
  ("DAG-record-binding", !binds dagRequest (dagDump.replace "4 2 2" "5 2 2")),
  ("DAG-unreachable-record-binding", !binds dagRequest
    (dagDump.replace "1 4294967295 4294967295 4294967295"
      "0 4294967295 4294967295 4294967295")),
  ("DAG-strong-next-rejected", !(parseRequest (dagRequest.replace "10 0" "9 0")).isOk),
  ("DAG-unknown-op-rejected", !(parseRequest (dagRequest.replace "10 0" "16 0")).isOk),
  ("DAG-unary-extra-child", !(parseRequest
    (dagRequest.replace "10 0 4294967295" "10 0 0")).isOk),
  ("DAG-nullary-extra-child", !(parseRequest
    (dagRequest.replace "2 4294967295 4294967295 0" "2 0 4294967295 0")).isOk),
  ("DAG-forward-child", !(parseRequest (dagRequest.replace "4 2 2" "4 2 4")).isOk),
  ("DAG-self-child", !(parseRequest (dagRequest.replace "4 2 2" "4 3 2")).isOk),
  ("DAG-missing-child", !(parseRequest
    (dagRequest.replace "4 2 2" "4 2 4294967295")).isOk),
  ("DAG-AP-bound", !(parseRequest
    (dagRequest.replace "2 4294967295 4294967295 0" "2 4294967295 4294967295 1")).isOk),
  ("DAG-extra-AP-field", !(parseRequest
    (dagRequest.replace "4 2 2 4294967295" "4 2 2 0")).isOk),
  ("DAG-uint32-bound", !(parseRequest
    (dagRequest.replace "4 2 2 4294967295" "4 2 2 4294967296")).isOk),
  ("DAG-invalid-root", !(parseRequest (dagRequest.replace "dag 5 3" "dag 5 5")).isOk),
  ("DAG-zero-nodes", !(parseRequest (dagRequest.replace "dag 5 3" "dag 0 0")).isOk),
  ("DAG-unreachable-invalid", !(parseRequest
    (dagRequest.replace "1 4294967295 4294967295 4294967295" "1 0 4294967295 4294967295")).isOk),
  ("DAG-missing-row", !binds dagRequest (dagDump.replace "0 1 0 3" "")),
  ("DAG-invalid-target", !binds dagRequest (dagDump.replace "0 1 0 3" "0 1 1 3")),
  ("DAG-duplicate-row", !binds dagRequest (dagDump.replace "0 1 0 3" "0 0 0 3")),
  ("DAG-declined-unvalidated", !binds dagRequest (dagRequest ++ " declined unsupported")),
  ("DAG-partial-unvalidated", !binds dagRequest (dagRequest ++ " states 1 0 end")),
  ("DAG-language-mismatch", !probe dagRequest (dagDump.replace "0 1 0 3" "0 1 0 2")),
  ("DAG-Buchi", probe (dagRequest.replace "parity" "buchi")
    ((dagRequest.replace "parity" "buchi") ++
      " states 2 1 0 0 0 1 1 0 1 0 1 1 0 1 0 1 1 0 0 end")),
  ("DAG-AP-order", !binds (dagRequest.replace "1 0 a" "1 1 a unused")
    (dagDump.replace "1 0 a" "1 1 unused a")),
  ("DAG-negative-objective", probe
    (dagRequest.replace "positive objective & 1 G F" "negative objective ! G F")
    (dagDump.replace "positive objective & 1 G F" "negative objective ! G F"))]

private def delay32 : Parity (Fin 2) (Fin 32) :=
  ⟨0, fun s a => (⟨(2*s.val + a.val) % 32, Nat.mod_lt _ (by decide)⟩,
    if s.val = 0 then 2 else 3)⟩

def protocolChecks : List (String × Bool) := [
  ("complete-parity-dump", probe request dump),
  ("CRLF-request", probe (request ++ "\r\n") dump),
  ("VT-whitespace", probe (request.replace " " "\x0b") (dump.replace " " "\x0b")),
  ("FF-whitespace", probe (request.replace " " "\x0c") (dump.replace " " "\x0c")),
  ("AP-order-mismatch", !probe "TV1 parity default 2 a b G F $a"
    "TV1 parity default 2 b a G F $a states 1 0 end"),
  ("AP-count-mismatch", !probe request (dump.replace "default 1" "default 2")),
  ("formula-mismatch", !probe request (dump.replace "G F $a" "F G $a")),
  ("undeclared-AP", !(parseRequest "TV1 parity default 1 a G F $b").isOk),
  ("duplicate-AP", !(parseRequest "TV1 parity default 2 a a G F $a").isOk),
  ("missing-edge", !probe request (dump.replace "0 1 0 3" "")),
  ("duplicate-edge", !probe request (dump.replace "0 1 0 3" "0 0 0 3")),
  ("invalid-target", !probe request (dump.replace "0 1 0 3" "0 1 1 3")),
  ("trailing-token", !probe request (dump ++ " extra")),
  ("language-mismatch", !probe request (dump.replace "0 1 0 3" "0 1 0 2")),
  ("complete-Buchi-dump", probe "TV1 buchi default 1 a G F $a"
    "TV1 buchi default 1 a G F $a states 2 1 0 0 0 1 1 0 1 0 1 1 0 1 0 1 1 0 0 end"),
  ("Buchi-source-acceptance-mismatch", !probe "TV1 buchi default 1 a G F $a"
    "TV1 buchi default 1 a G F $a states 1 1 0 0 0 1 0 1 0 0 end"),
  ("non-Buchi-language-rejected", !probe "TV1 buchi general 1 a F G $a"
    "TV1 buchi general 1 a F G $a states 1 1 0 0 0 1 0 1 0 1 end"),
  ("Buchi-constant-negative-recurrence", probe "TV1 buchi default 1 b ! G F & $b X 0"
    "TV1 buchi default 1 b ! G F & $b X 0 states 1 1 0 0 0 1 0 1 0 1 end"),
  ("Buchi-positiveb-fallback-still-checks-language", !probe "TV1 buchi general 1 b ! G F & $b X 0"
    "TV1 buchi general 1 b ! G F & $b X 0 states 1 0 0 0 0 0 0 1 0 0 end"),
  ("Buchi-nonpositive-cosafety", probe "TV1 buchi default 2 a b U 1 i $b ^ $b G $a"
    "TV1 buchi default 2 a b U 1 i $b ^ $b G $a states 2 0 1 0 0 1 0 0 1 1 0 0 2 1 0 0 3 0 0 1 0 1 1 1 1 1 1 1 2 1 1 1 3 1 1 end"),
  ("compact-different-state-count", checkCompact (singleton 1) (alternating 3 0)),
  ("compact-disagreement", !checkCompact (singleton 1) infLetters),
  ("compact-Buchi-frequency", checkBuchiCompact allBuchi alternatingBuchi),
  ("sparse-delay-product", check delay32 delay32)] ++ dagChecks

end Tlsf.Dpa.Validation
