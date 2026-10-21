import dev.veriloggraph.Grammar;
import dev.veriloggraph.Production;
import dev.veriloggraph.Symbol;
import dev.veriloggraph.TokenCatalog;
import java.util.LinkedHashMap;

/** Emits the token-kind grammar imported by the VerilogGraph prototype. */
public final class ExportAnnexTable {
  public static void main(String[] args) {
    var catalog = TokenCatalog.Companion.bundled();
    Grammar grammar = Grammar.Companion.bundled(catalog);
    var names = new LinkedHashMap<String, Integer>();
    for (Production production : grammar.getProductions()) {
      names.computeIfAbsent(production.getLeft(), ignored -> names.size());
    }
    for (Production production : grammar.getProductions()) {
      for (Symbol symbol : production.getRight()) {
        if (symbol instanceof Symbol.Rule rule) {
          names.computeIfAbsent(rule.getName(), ignored -> names.size());
        }
      }
    }

    System.out.println("R " + names.size() + " " +
                       grammar.getProductions().size());
    for (int index = 0; index < catalog.getKinds().size(); ++index) {
      System.out.println("K " + index + " " +
                         catalog.getKinds().get(index).getName());
    }
    for (var entry : names.entrySet()) {
      System.out.println("N " + entry.getValue() + " " + entry.getKey());
    }
    for (Production production : grammar.getProductions()) {
      var line = new StringBuilder("P " + names.get(production.getLeft()) +
                                   " " + production.getRight().size());
      for (Symbol symbol : production.getRight()) {
        if (symbol instanceof Symbol.Rule rule) {
          line.append(" R").append(names.get(rule.getName()));
        } else if (symbol instanceof Symbol.Token token) {
          line.append(" T").append(
              catalog.getKinds().indexOf(catalog.getByName().get(token.getKind())));
        }
      }
      System.out.println(line);
    }
  }
}
