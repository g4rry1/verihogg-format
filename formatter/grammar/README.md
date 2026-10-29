# IEEE 1800-2023 Annex A import

`../src/pipeline/annex_a/table.inc` contains 723 named syntax rules, 905
generated helper rules, and 3409 productions after expansion of optional and
repeated expressions and one extraction correction. Its source
is `/home/dmitrii/veriloggraph/src/main/resources/ieee1800-2023-annex-a-styled.txt`
(SHA-256 `4c68aa70939d2ed900e8696cbfd471df56146a8ca0ef400b6c8927688cf1d266`).

VerilogGraph's `SOURCE.txt` identifies the IEEE 1800-2023 PDF and records its
SHA-256 as `203fbcccbbae90cef401a3acd31835c8cd1507e8f12b2e069046d4f316e317c9`.
`tools/extract_ieee_pdf.py` extracts pages 1173–1217 with `pdftohtml`, retains
the red terminal text, and checks for 736 conventionally spelled rule headings.
The 14 remaining source headings include timing checks beginning with `$` and
two malformed separators normalized by the Kotlin importer. The 27 lexical
rules represented directly by slang token kinds are absent from the C++ rule
table. The importer reports no unresolved symbols reachable from `source_text`
or `library_text`. The source hash and these checks establish provenance and
structural completeness; the IEEE PDF is not present locally for a character
by character comparison.

The styled extraction loses `static` inside the optional part of
`constraint_prototype` and turns the PDF footnote marker `8,11` into a comma.
The independent plain-text extraction at
`/home/dmitrii/veriloggraph/src/main/resources/ieee1800-2023-annex-a.txt`
retains `[ static ] constraint [ dynamic_override_specifiers ]` and the
footnote marker. `table_from_export.py` corrects this imported production to
match the Annex A text. It asserts the broken shape before applying the
correction, so a changed upstream extraction cannot silently receive it.

To regenerate the table, build VerilogGraph, compile `ExportAnnexTable.java`
against its classes and the Kotlin runtime, then run:

```sh
java -cp '<veriloggraph classes>:<veriloggraph resources>:<Kotlin runtime>:formatter/grammar' ExportAnnexTable > annex.table
python3 formatter/grammar/table_from_export.py annex.table formatter/src/pipeline/annex_a/table.inc
```

The token inventory was imported from slang revision
`dcc7ee97fb14f9be003de71e100d0c9601a993c9`. `SVParser` maps terminal
names to the installed slang token kinds, so changed enum ordinals do not
change the grammar. An unrecognized token kind produces a diagnosed fallback.
Lexemes and trivia continue to come from slang tokens.

`TreeUnwrapper::SVParser` owns temporary Earley charts while it consumes tokens
and emits `UnwrappedLine` objects. There is no separate prefix recognizer or
completed token range pass. Structural headers and their body items use
separate chart scopes, so ordinary large modules, packages, classes, and
functions do not require a whole-file chart. The viable declaration prefix
validates a package, class, function, or task header through its first
semicolon; the corresponding Annex A item rules validate body items
individually. Function and task bodies stop accepting declarations after an
item that can only be a statement under Annex A. Attribute prefixes are parsed
with Annex A's `attribute_instance` rule before starting the decorated item's
chart, including attributes around `package_item`. Annex A FIRST sets select
construction families after complete attribute prefixes. Header charts find
module, interface, and program boundaries, including package imports before
ports. A two million item guard applies to pathological ambiguity, with an
explicit diagnostic. Compiler directives are consumed inside the current
parser flow without advancing Annex A; unexpanded macros and malformed items
use diagnosed fallback and retain their source tokens. No persistent syntax
tree is built.

Conditional compiler branches now copy the active grammar scopes as well as the
layout state. Compatible branches resume one grammar continuation after
`endif`. Named headers, condition expressions, case expressions, and `for`
header segments advance Annex A rules while their tokens are emitted. The
formatter still uses explicit block delimiters and source-preserving fallback
when the available token stream cannot be parsed by those rules.

When a macro or malformed item interrupts a nested Annex A scope, `SVParser`
restores the enclosing chart to the start of that item and advances its expected
item nonterminal once. The original tokens are retained in their existing
lines, and a fallback diagnostic identifies the interruption. This lets a
package, class, function, or case continue from the next item without replaying
its earlier tokens. An unknown backtick token at the start of an item is
handled through its semicolon or source line, stopping before the enclosing
block close. Compiler directives suspend the active chart without consuming a
grammar item.
