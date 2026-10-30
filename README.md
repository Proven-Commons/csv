# csv: a CSV parser and printer, with a proved round trip

A CSV parser and printer in Lean, following RFC 4180. The parser reads a CSV text into a document, a list of records of fields; the printer writes a document back in one fixed canonical form, quoting a field exactly when its text holds a comma, a quote, a CR, or an LF, and ending every record with CRLF. The main claim is proved: parsing what the printer wrote returns the same document. The tests run the parser against the examples of RFC 4180, against Python's `csv` module, and against a strict Python reading of the grammar; see `tests/TEST-RESULTS.md` for the counts.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Csv/Spec.lean`) has been added by a reviewer, so this is not verified.

## What is proved

The definitions are in `Csv/Value.lean` (the data model, the printer, and the well-formedness rule) and `Csv/Parse.lean` (the parser). The proofs are in `Csv/Proofs/RoundTrip.lean`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed document gives the document back. | `Csv.Proofs.parse_print` |
| The same, one record at a time: the fields of a printed record read back whole, followed by the text after its CRLF. | `Csv.Proofs.parseFields_printFields` |
| Reading back a doubled-quote body gives the field back, quotes and all. | `Csv.Proofs.parseQuoted_doubleQuotes` |
| Reading back a plain field run gives the field back whole, when what follows cannot extend the run. | `Csv.Proofs.takePlain_append` |

A document is well formed when every record holds at least one field. Field texts need no further condition. `parse_print` checks against the axioms `propext` and `Quot.sound` only, which a reader can confirm with `#print axioms Csv.Proofs.parse_print`.

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- That the parser accepts every text the grammar allows, and rejects every text it forbids. The round trip does not need either, so neither is proved. The RFC examples and the differential tests check that behaviour instead, and the results file records the outcome, including any failure.
- Anything about columns or headers. A header row is a record like any other; there is no mapping from a record to named values, and no lookup.
- Other dialects: semicolon or tab delimiters, LF-only line endings on reading, spaces trimmed around fields. Reading takes CRLF as the only record separator, as `SPEC.md` states.
- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, and the check that a code is a Unicode scalar value. The tests cover them, malformed requests included.
- Speed. The code works on lists of characters, which suits proofs, not large data. The parser also bounds its field and record counts by the length of the input text, which very wide or very long documents can reach.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- Python's standard library, as the oracle in the differential tests, and RFC 4180, as the text whose examples the fixed cases use. The results file names the versions used.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 97,44,98" | .lake/build/bin/csv
```

That request is the text `a,b` as character codes, and the answer is `ok:97,44,98,13,10`, the canonical print with its closing CRLF. A text the parser rejects, such as the single code `10` (a bare line feed), answers `none`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

## Re-check it

Needs Linux, elan, and Python 3.11 or later.

```
lake build
grep -rn "sorry" --include="*.lean" Csv Main.lean Csv.lean
python3 tests/run_tests.py
```

The grep should print nothing: there is no `sorry` anywhere. The test script rebuilds the tool, runs the fixed cases from RFC 4180, runs the canonical round trips against Python's `csv` module, runs the differential tests against the strict Python oracle with a fixed seed, and writes the counts to `tests/TEST-RESULTS.md`.
