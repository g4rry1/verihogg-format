#!/usr/bin/env python3
"""Convert ExportAnnexTable output into the C++ grammar table."""

import pathlib
import sys


def main() -> None:
    source = pathlib.Path(sys.argv[1])
    destination = pathlib.Path(sys.argv[2])
    rows = source.read_text(encoding="utf-8").splitlines()
    _, rule_count, production_count = rows[0].split()
    names = [""] * int(rule_count)
    token_names = []
    productions = []
    symbols = []
    for row in rows[1:]:
        fields = row.split()
        if fields[0] == "K":
            assert int(fields[1]) == len(token_names)
            token_names.append(fields[2])
        elif fields[0] == "N":
            names[int(fields[1])] = fields[2]
        elif fields[0] == "P":
            left, count = map(int, fields[1:3])
            assert len(fields) == count + 3
            productions.append((left, len(symbols), count))
            symbols.extend(
                int(value[1:]) if value[0] == "R" else -1 - int(value[1:])
                for value in fields[3:]
            )
        else:
            raise ValueError(f"Unexpected export row: {row}")
    assert len(productions) == int(production_count)
    assert all(names)
    assert len(token_names) == 352
    assert len(symbols) < 65536

    # The styled PDF extraction lost the terminal inside "[ static ]" and
    # treated the footnote marker "8,11" as a literal comma. The independent
    # plain-text extraction retains the production's words (see README.md).
    # Repair that one imported production before emitting the C++ table.
    rule = names.index("constraint_prototype")
    optional_static = names.index("@constraint_prototype_206")
    expected = [
        names.index("@constraint_prototype_205"),
        optional_static,
        names.index("@constraint_prototype_207"),
        -1 - token_names.index("Comma"),
        -1 - token_names.index("StaticKeyword"),
        -1 - token_names.index("ConstraintKeyword"),
        names.index("constraint_identifier"),
        -1 - token_names.index("Semicolon"),
    ]
    matches = [i for i, (left, offset, count) in enumerate(productions)
               if left == rule and symbols[offset:offset + count] == expected]
    assert len(matches) == 1, "constraint_prototype extraction changed"
    static_choices = [count for left, _, count in productions
                      if left == optional_static]
    assert static_choices and all(count == 0 for count in static_choices)
    # Append the corrected right-hand side to keep every other production's
    # offset stable. The original broken right-hand side becomes unreachable.
    corrected = [expected[0], optional_static, expected[5], expected[2],
                 expected[6], expected[7]]
    productions[matches[0]] = (rule, len(symbols), len(corrected))
    symbols.extend(corrected)
    productions.append((optional_static, len(symbols), 1))
    symbols.append(-1 - token_names.index("StaticKeyword"))

    with destination.open("w", encoding="utf-8") as output:
        output.write(
            "// Generated from IEEE 1800-2023 Annex A via veriloggraph GrammarImporter.\n"
            "// Source provenance: formatter/grammar/README.md\n"
            "static constexpr std::string_view kTokenNames[] = {\n"
        )
        for name in token_names:
            output.write(f'    "{name}",\n')
        output.write("};\nstatic constexpr std::string_view kRuleNames[] = {\n")
        for name in names:
            escaped = name.replace("\\", "\\\\").replace('"', '\\"')
            output.write(f'    "{escaped}",\n')
        output.write("};\nstatic constexpr Production kProductions[] = {\n")
        for left, offset, count in productions:
            output.write(f"    {{{left}, {offset}, {count}}},\n")
        output.write("};\nstatic constexpr int16_t kSymbols[] = {\n")
        for index in range(0, len(symbols), 20):
            output.write(
                "    " + ", ".join(map(str, symbols[index:index + 20])) + ",\n"
            )
        output.write("};\n")


if __name__ == "__main__":
    main()
