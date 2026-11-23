# Reproducing the checks

Run python six_core.py in this directory with Python 3. The exact computation checks all three rows and the tight-set obstruction in the middle row.

With Pandoc and Tectonic on PATH, run python build_preprint.py --logs /path/to/build-logs to typeset the two manuscripts and two companions. Use a new log directory outside the edition. The first run can require network access for TeX resources. The builder performs three passes per document. In the repository, python scripts/verify_preprint.py verifies the frozen distribution without typesetting it again.

The formal source archive in 05_formalization contains the pinned Lake manifest, the toolchain, the sources and both axiom checkers. From its lean directory, run:

    lake exe cache get
    lake build SplitGapII SplitGapIIAudit
    lake env lean SplitGapIIAudit.lean
    lake env lean AllAxioms.lean
