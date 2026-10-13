# Provenance and verification evidence

- `upstream.json`: pinned upstream revision/license, original source hashes,
  unchanged-file hashes and mappings for the derived current proof.
- [upstream/](upstream/README.md): unchanged original transition source for baseline extraction.
- `baseline-audit.json`: reproducible 25-state audit, including finite reachability
  witnesses and all 300 ordered state-conflict reasons.
- `scan-sharing.json`: exact settings and counts for the final replayable search,
  including its bounded screening scope and selected candidate.
- `optimization23.json`: compact settings and results of the 23-state searches;
  these are finite experiments, not a minimality certificate.
- `verification24.json`: independent finite verification of the selected literal table.
- `proof24.json`: successful Lean build and axiom inspection, pinned to current source hashes.

These are compact verification records, not raw execution logs. Reproduce with
`tools/audit.py`, `tools/verify24.py`, `tools/search_scans.py` and the
[Lean commands](../formal/README.md). Search frontiers, binaries and dependency
caches remain outside Git.
