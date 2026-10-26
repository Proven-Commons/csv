# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.12.3 `csv` module, plus a strict reading of the plan rules written in the harness
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Fixed cases (RFC 4180 section 2 and plan edges): 36 of 36 agreements
- Python csv round trips: 2500 documents, 5000 of 5000 agreements
- Documents where Python csv writes a lone empty field as "" and this printer writes a bare CRLF (named difference): 91
- Differential inputs: 5000
- Differential agreements: 5000
- Malformed requests answered error: 12 of 12
- Requests with no codes answered ok:: 2 of 2
- Failures: 0
