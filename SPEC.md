# Specification: csv

A CSV parser and printer in Lean, following RFC 4180. A reviewer who did not write this specification approves it, together with any statement file a reviewer adds later. No such file exists yet, so nothing here counts toward the verified bar yet.

Text is `List Char`. A Lean `Char` is one Unicode scalar value.

## Documents

One data model:

- a field is text, a list of characters;
- a record is a list of fields;
- a document is a list of records.

Any field text is allowed in the model, including commas, quotes, carriage returns, and line feeds. A header row is a record like any other at this layer: nothing here maps a record to column names.

## Reading

The parser reads this grammar:

- Records are split by CRLF. The last record may end without a CRLF. Empty input reads as zero records, and a trailing CRLF after the last record does not create an extra record. A single CRLF alone is one record with one empty field.
- An unquoted field holds any run of characters except comma, quote, CR, and LF. It ends at a comma, a CRLF, or the end of the input.
- A quoted field starts with a quote at the start of a field. Inside it any character may appear, including commas, CR, and LF; a quote is written twice and reads as one quote. The closing quote must be followed by a comma, a CRLF, or the end of the input.
- Everything else is rejected: a bare CR not followed by LF outside a quoted field, a bare LF outside a quoted field, a quote in the middle of an unquoted field, a quoted field that never closes, and any character after a closing quote other than the three followers above.
- Spaces are field data. Nothing is trimmed, on either side.

Two deliberate choices sit inside these rules. Line endings other than CRLF are not read: RFC 4180 names CRLF as the record separator, and this slice takes the strict reading, so a text broken by bare LF is rejected rather than read in a second dialect. And the reader takes the text as it stands: it does not skip blank records or guess at a header.

## Printing

The printer writes one canonical form:

- A field is quoted exactly when it holds a comma, a quote, a CR, or an LF. Quotes inside a quoted field are written twice. Any other field is written as it stands, empty fields included: a record of one empty field prints as a bare CRLF.
- Fields in a record are joined by commas.
- Every record ends with CRLF, the last record included. Zero records print as the empty text.

## The claim

The proved claim is a round trip: for every well formed document, parsing what the printer wrote returns the same document. Well formed means every record holds at least one field. Field texts need no further condition.

No claim is made that the parser accepts every text the grammar allows, or rejects every text it forbids, beyond what the round trip needs. The test suite checks that behaviour against the examples of RFC 4180, against Python's `csv` module on the canonical forms, and against a strict Python reading of the rules above on random and mutated texts. The results record the counts.

## The command-line tool

`Main.lean` reads one request per line. The only operation is `parse`: the request is the word `parse`, a space, and the character codes of a CSV text as comma-separated decimal numbers. The answer is `ok:` followed by the character codes of the canonical print of the parsed document, or `none` when the text is rejected. A malformed request line prints `error`. Codes that are not Unicode scalar values make the request malformed.
