# IEEE 1800-2023 Annex A import

`../src/pipeline/annex_a/table.inc` contains 723 named syntax rules, 905
generated helper rules, and 3408 productions after expansion of optional and
repeated expressions. Its source
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
separate chart scopes, so ordinary large modules do not require a whole-file
chart. A two million item guard applies to pathological ambiguity, with an
explicit diagnostic. Compiler directives are consumed inside the current
parser flow without advancing Annex A; unexpanded macros and malformed items
use diagnosed fallback and retain their source tokens. No persistent syntax
tree is built.
