#!/usr/bin/env python3
"""Tests for the Lean CSV parser and printer.

Three parts.

1. Fixed cases: the examples from section 2 of RFC 4180, plus the
   edge cases the plan names: empty input, a lone CRLF, quoted
   empty fields, doubled quotes, trailing commas, and the rejected
   shapes (a bare CR or LF outside quotes, a quote in the middle of
   a plain field, text after a closing quote, an unterminated
   quoted field).

2. Canonical round trips against Python's `csv` module, with a
   recorded seed. Random documents are built in Python, written by
   `csv.writer` (delimiter comma, QUOTE_MINIMAL, line terminator
   CRLF), and the Lean tool must parse that text and answer with
   the canonical print of the same document; it must give the same
   answer for the canonical print itself. One named difference is
   counted, not failed: `csv.writer` writes a record of one empty
   field as `""` followed by CRLF, so the row cannot be mistaken
   for a blank line, while this printer writes the bare CRLF that
   the plan states. Both texts parse to the same document here.
   (The module's reader is not used as an oracle: it reads a blank
   line as an empty record, where this grammar reads one record
   with one empty field.)

3. A differential run against a strict Python oracle written in
   this harness from the plan rules (Python's `csv` reader is more
   lenient than this slice, so it is not the accept/reject oracle).
   Random texts over an alphabet heavy in the special characters,
   and mutations of canonical texts, must be rejected by both
   sides, or accepted with the same canonical reprint.

   Malformed request lines must be answered `error`.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests, input
written and closed, output drained until the process exits. It
builds the executable first, writes tests/TEST-RESULTS.md, and
exits non-zero if any check fails. It needs Python 3.11 or later.
"""

import argparse
import csv
import io
import random
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "csv"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 900
BUILD_TIMEOUT = 3600
CHUNK = 2000

SEED_DEFAULT = 20261026


def codes(text):
    return ",".join(str(ord(c)) for c in text)


def request(text):
    return "parse " + codes(text)


def run_tool(lines, timeout=TIMEOUT):
    """Run the tool on a batch of request lines.

    Returns (answers, problem). No right answer is longer than its
    request plus a small constant per record, so output past twice
    the input plus 64 bytes a line is stopped, not read until
    memory runs out.
    """
    data = "".join(line + "\n" for line in lines)
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (len(lines) + 1)
    try:
        proc = subprocess.Popen(
            [str(EXE)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as e:
        return [], f"could not run {EXE}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [
        threading.Thread(target=feed),
        threading.Thread(target=drain, args=(proc.stdout, out, limit)),
        threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20)),
    ]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(
            bytes(err).decode("utf-8", "backslashreplace").splitlines()[-3:]
        )
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    if len(answers) != len(lines) and not problem:
        problem = f"tool gave {len(answers)} answers for {len(lines)} requests"
    return answers, problem


def ask_all(lines):
    """Chunked run_tool. Answers align with lines, or None entries."""
    answers = []
    problems = []
    for i in range(0, len(lines), CHUNK):
        chunk = lines[i : i + CHUNK]
        ans, problem = run_tool(chunk)
        if problem:
            problems.append(problem)
            ans = ans + [None] * (len(chunk) - len(ans))
        answers += ans
    return answers, problems


# ---------------------------------------------------------------- the
# Python mirrors of the Lean rules.


def canonical_field(f):
    if any(c in f for c in ',"\r\n'):
        return '"' + f.replace('"', '""') + '"'
    return f


def canonical(doc):
    """The canonical print of a document, as the plan states it."""
    return "".join(
        ",".join(canonical_field(f) for f in rec) + "\r\n" for rec in doc
    )


def oracle_parse(text):
    """The strict reading of the plan rules. A document, or None.

    Mirrors the Lean parser: records split by CRLF, the last record
    may end without one, empty input is zero records, a quoted
    field may hold anything with quotes doubled, and the closing
    quote must be followed by a comma, a CRLF, or the end.
    """
    n = len(text)

    def field(i):
        # (value, index of the follower) or None. The follower is a
        # comma, the CR of a CRLF, or the end of the text.
        if i < n and text[i] == '"':
            out = []
            j = i + 1
            while True:
                if j >= n:
                    return None
                c = text[j]
                if c == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        out.append('"')
                        j += 2
                    else:
                        j += 1
                        break
                else:
                    out.append(c)
                    j += 1
            if (
                j >= n
                or text[j] == ","
                or (text[j] == "\r" and j + 1 < n and text[j + 1] == "\n")
            ):
                return ("".join(out), j)
            return None
        j = i
        while j < n and text[j] not in ',"\r\n':
            j += 1
        if j < n and text[j] == '"':
            return None
        if j < n and text[j] == "\n":
            return None
        if j < n and text[j] == "\r" and not (
            j + 1 < n and text[j + 1] == "\n"
        ):
            return None
        return (text[i:j], j)

    def record(i):
        # (fields, index after the record, ended by CRLF) or None.
        fields = []
        while True:
            r = field(i)
            if r is None:
                return None
            f, j = r
            fields.append(f)
            if j >= n:
                return (fields, j, False)
            if text[j] == ",":
                i = j + 1
                continue
            return (fields, j + 2, True)

    if n == 0:
        return []
    doc = []
    i = 0
    while True:
        r = record(i)
        if r is None:
            return None
        fields, j, crlf = r
        doc.append(fields)
        if not crlf:
            return doc
        i = j
        if i >= n:
            return doc


# ---------------------------------------------------------------- the
# fixed cases.

CRLF = "\r\n"

# (input, expected canonical reprint); None means rejected.
FIXED = [
    # RFC 4180, section 2: the opening example, with header row.
    (
        "field_name,field_name,field_name" + CRLF
        + "aaa,bbb,ccc" + CRLF
        + "zzz,yyy,xxx" + CRLF,
        "field_name,field_name,field_name" + CRLF
        + "aaa,bbb,ccc" + CRLF
        + "zzz,yyy,xxx" + CRLF,
    ),
    # Section 2, point 2: the last record may end without a CRLF.
    ("aaa,bbb,ccc" + CRLF + "zzz,yyy,xxx", "aaa,bbb,ccc" + CRLF + "zzz,yyy,xxx" + CRLF),
    # Section 2, point 4: spaces are part of a field.
    ("aaa, bbb,ccc" + CRLF, "aaa, bbb,ccc" + CRLF),
    # Section 2, point 5: a field with an embedded comma is quoted.
    # Quotes the text did not need are dropped on the reprint: the
    # canonical form quotes only the fields that hold a special
    # character.
    ('"aaa","b,b","ccc"' + CRLF, 'aaa,"b,b",ccc' + CRLF),
    # Section 2, point 6: a field with an embedded line break.
    (
        '"aaa","b' + CRLF + 'bb","ccc"' + CRLF + "zzz,yyy,xxx" + CRLF,
        'aaa,"b' + CRLF + 'bb",ccc' + CRLF + "zzz,yyy,xxx" + CRLF,
    ),
    # Section 2, point 7: quotes inside a quoted field are doubled.
    ('"aaa","b""bb","ccc"' + CRLF, 'aaa,"b""bb",ccc' + CRLF),
    # The plan's edges.
    ("", ""),
    (CRLF, CRLF),
    (CRLF + CRLF, CRLF + CRLF),
    ('""', CRLF),
    ('"a"', "a" + CRLF),
    ('""""', '""""' + CRLF),
    ('"a""b"', '"a""b"' + CRLF),
    (",,", ",," + CRLF),
    ("a,", "a," + CRLF),
    (",a", ",a" + CRLF),
    ('"",""', "," + CRLF),
    ("a", "a" + CRLF),
    ("a,b" + CRLF + "c", "a,b" + CRLF + "c" + CRLF),
    ('"x\ny"', '"x\ny"' + CRLF),
    ('"x\ry"', '"x\ry"' + CRLF),
    ('" lead "', " lead " + CRLF),
    # Rejected shapes.
    ("a\nb", None),
    ("a\rb", None),
    ("a\r", None),
    ("\n", None),
    ("\r", None),
    ('"a', None),
    ('"a""', None),
    ('"a"x', None),
    ('"a" "b"', None),
    ('"a"\n', None),
    ('"a"\r', None),
    ('a"b', None),
    ('ab"cd"', None),
    ("a,\r", None),
]

MALFORMED = [
    "bogus 1",
    "parse 12a",
    "parse 1114112",
    "parse 55296",
    "parse 1,,2",
    "parse  97",
    "parse 97 ",
    "PARSE 97",
    "parse -1",
    "parse 0x41",
    "parse 97 98",
    "parse 1.5",
]


def run_fixed():
    lines = []
    failures = []
    answers, problems = ask_all([request(t) for t, _ in FIXED])
    for problem in problems:
        failures.append(f"fixed cases: tool problem: {problem}")
    agree = 0
    for (text, want), ans in zip(FIXED, answers):
        want_ans = "none" if want is None else "ok:" + codes(want)
        if ans == want_ans:
            agree += 1
        else:
            failures.append(f"fixed case {text!r}: want {want_ans!r}, got {ans!r}")
    lines.append(
        f"Fixed cases (RFC 4180 section 2 and plan edges): "
        f"{agree} of {len(FIXED)} agreements"
    )
    return lines, failures


FIELD_CHARS = list("abcXYZ 019") + [",", '"', "\r", "\n", "\t", "é", ""]


def rand_field(rng):
    return "".join(rng.choice(FIELD_CHARS) for _ in range(rng.randrange(0, 11)))


def rand_doc(rng):
    doc = []
    for _ in range(rng.randrange(0, 5)):
        doc.append([rand_field(rng) for _ in range(rng.randrange(1, 6))])
    return doc


def python_csv_text(doc):
    buf = io.StringIO(newline="")
    w = csv.writer(
        buf,
        delimiter=",",
        quotechar='"',
        quoting=csv.QUOTE_MINIMAL,
        lineterminator="\r\n",
    )
    w.writerows(doc)
    return buf.getvalue()


def run_python_csv(seed, count):
    lines = []
    failures = []
    rng = random.Random(seed)
    docs = [rand_doc(rng) for _ in range(count)]
    lines_in = []
    wants = []
    diffs = 0
    for doc in docs:
        canon = canonical(doc)
        py_text = python_csv_text(doc)
        if py_text != canon:
            # The one named difference: a record of one empty field
            # is written "" by the module. Any other difference is a
            # failure of this harness's mirror, and is reported.
            if any(rec == [""] for rec in doc):
                diffs += 1
            else:
                failures.append(
                    f"csv module text differs with no lone empty field: {doc!r}"
                )
        want = "ok:" + codes(canon)
        lines_in.append(request(py_text))
        wants.append(want)
        lines_in.append(request(canon))
        wants.append(want)
    answers, problems = ask_all(lines_in)
    for problem in problems:
        failures.append(f"python csv: tool problem: {problem}")
    agree = 0
    for want, ans in zip(wants, answers):
        if ans == want:
            agree += 1
        else:
            failures.append(f"python csv case: want {want!r}, got {ans!r}")
    lines.append(
        f"Python csv round trips: {len(docs)} documents, "
        f"{agree} of {len(wants)} agreements"
    )
    lines.append(
        "Documents where Python csv writes a lone empty field as "
        f'"" and this printer writes a bare CRLF (named difference): {diffs}'
    )
    return lines, failures


SOUP_CHARS = list("ab,") + ['"', "\r", "\n", " ", "0"]


def run_differential(seed, count):
    lines = []
    failures = []
    rng = random.Random(seed + 1)
    inputs = []
    for _ in range(count):
        length = rng.randrange(0, 41)
        inputs.append("".join(rng.choice(SOUP_CHARS) for _ in range(length)))
    mut_inputs = []
    for _ in range(count):
        text = canonical(rand_doc(rng))
        chars = list(text)
        for _ in range(rng.randrange(1, 4)):
            if not chars:
                chars.append(rng.choice(SOUP_CHARS))
                continue
            op = rng.randrange(0, 3)
            pos = rng.randrange(0, len(chars) + (1 if op == 0 else 0))
            if op == 0:
                chars.insert(pos, rng.choice(SOUP_CHARS))
            elif op == 1:
                chars[pos] = rng.choice(SOUP_CHARS)
            else:
                del chars[pos]
        mut_inputs.append("".join(chars))
    inputs += mut_inputs
    wants = []
    for text in inputs:
        doc = oracle_parse(text)
        wants.append("none" if doc is None else "ok:" + codes(canonical(doc)))
    answers, problems = ask_all([request(t) for t in inputs])
    for problem in problems:
        failures.append(f"differential: tool problem: {problem}")
    agree = 0
    for text, want, ans in zip(inputs, wants, answers):
        if ans == want:
            agree += 1
        else:
            failures.append(f"differential {text!r}: want {want!r}, got {ans!r}")
    lines.append(f"Differential inputs: {len(inputs)}")
    lines.append(f"Differential agreements: {agree}")
    return lines, failures


def run_malformed():
    lines = []
    failures = []
    answers, problems = ask_all(MALFORMED)
    for problem in problems:
        failures.append(f"malformed: tool problem: {problem}")
    bad_ok = 0
    for line, ans in zip(MALFORMED, answers):
        if ans == "error":
            bad_ok += 1
        else:
            failures.append(f"malformed {line!r}: want error, got {ans!r}")
    lines.append(f"Malformed requests answered error: {bad_ok} of {len(MALFORMED)}")
    # A request with no codes at all is the empty text: zero
    # records, printed as the empty text, not malformed.
    empty_ok = 0
    answers, _ = ask_all(["parse", "parse "])
    for ans in answers:
        if ans == "ok:":
            empty_ok += 1
        else:
            failures.append(f"empty request: want ok:, got {ans!r}")
    lines.append(f"Requests with no codes answered ok:: {empty_ok} of 2")
    return lines, failures


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=SEED_DEFAULT)
    ap.add_argument("--count", type=int, default=2500)
    args = ap.parse_args()

    build = subprocess.run(
        ["lake", "build"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=BUILD_TIMEOUT,
    )
    if build.returncode != 0:
        print(build.stdout)
        print(build.stderr)
        print("lake build failed")
        return 1

    all_lines = []
    all_failures = []
    for part in (
        run_fixed(),
        run_python_csv(args.seed, args.count),
        run_differential(args.seed, args.count),
        run_malformed(),
    ):
        lines, failures = part
        all_lines += lines
        all_failures += failures

    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    ).stdout.strip()

    out = ["# Test results", ""]
    out.append("Written by `tests/run_tests.py`. Rerun it to check these numbers.")
    out.append("")
    out.append(
        f"- Oracle: Python {sys.version.split()[0]} `csv` module, plus a strict "
        "reading of the plan rules written in the harness"
    )
    out.append(f"- Lean: {lean_version}")
    out.append(f"- Seed: {args.seed}")
    for line in all_lines:
        out.append(f"- {line}")
    out.append(f"- Failures: {len(all_failures)}")
    for failure in all_failures[:50]:
        out.append(f"- FAILURE: {failure}")
    RESULTS.write_text("\n".join(out) + "\n", encoding="utf-8")
    print("\n".join(out))
    return 0 if not all_failures else 1


if __name__ == "__main__":
    sys.exit(main())
