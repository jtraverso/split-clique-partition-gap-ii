# Verification and regeneration

Python 3.10 or later suffices for verify_edition.py, six_core.py and eight_core.py. Run these programs with Python from this directory. The first compares the sealed bytes with the SHA-256 manifest, validates the formal evidence, and executes both exact finite examples. A new Lean run requires elan, the pinned dependencies and the commands in the formalization companion.

To regenerate the documents in a separate directory, run the following from this directory, replacing OUTPUT with a directory outside the edition.

    python build_preprint.py --output OUTPUT --pandoc pandoc --tectonic tectonic

Tested with Pandoc 3.11 (minimum 3.8 for the syntax-highlighting option), Tectonic 0.17.0 and its default v33 bundle. The first run may download TeX resources. The output includes TeX, figures, four PDFs and the compiler logs. This regenerates content. The manifest identifies the specific distributed PDF bytes, which can also depend on engine metadata.

The historical source package version 0.2.0 identifies the unchanged base of the Lean library. The edition 1.1 formal archive adds SplitGapII11.lean. Its two declarations concern numerical implications. The manuscript gives the combinatorial proof of protected recovery and eight_core.py verifies the sharp example without relying on a solver.
