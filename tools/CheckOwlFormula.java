import java.nio.file.Files;
import java.nio.file.Path;
import owl.ltl.parser.LtlParser;

// Use the unmodified official release jar, not a rebuilt Owl. Verify the CLI's
// first-occurrence alphabet and the disappearance of the false AP primer.
public class CheckOwlFormula {
  public static void main(String[] args) throws Exception {
    for (String prefix : args) {
      var aps = Files.readAllLines(Path.of(prefix + ".aps"));
      var expected = LtlParser.parse(Files.readString(Path.of(prefix + ".ltl")), aps);
      var actual = LtlParser.parse(Files.readString(Path.of(prefix + ".owl.ltl")));
      // LabelledFormula.of drops trailing unused declarations in Owl 21.0.
      if (!expected.equals(actual) ||
          !actual.atomicPropositions().equals(aps.subList(0, actual.atomicPropositions().size()))) {
        throw new IllegalStateException("Formula/alphabet mismatch: " + prefix);
      }
      System.out.println("checked " + Path.of(prefix).getFileName());
    }
    System.out.println(args.length + " formulas and ordered alphabets match");
  }
}
