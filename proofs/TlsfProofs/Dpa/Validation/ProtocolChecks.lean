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

private def delay32 : Parity (Fin 2) (Fin 32) :=
  ⟨0, fun s a => (⟨(2*s.val + a.val) % 32, Nat.mod_lt _ (by decide)⟩,
    if s.val = 0 then 2 else 3)⟩

def protocolChecks : List (String × Bool) := [
  ("complete-parity-dump", probe request dump),
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
  ("Buchi-positiveb-required", !probe "TV1 buchi general 1 a F G $a"
    "TV1 buchi general 1 a F G $a states 1 1 0 0 0 1 0 1 0 1 end"),
  ("compact-different-state-count", checkCompact (singleton 1) (alternating 3 0)),
  ("compact-disagreement", !checkCompact (singleton 1) infLetters),
  ("compact-Buchi-frequency", checkBuchiCompact allBuchi alternatingBuchi),
  ("sparse-delay-product", check delay32 delay32)]

end Tlsf.Dpa.Validation
