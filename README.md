# Stability of the Clique Partition Gap in Split Graphs

**Paper II in the series on clique partition gaps in split graphs** · Juan Pablo Traverso Gianini · Preprint 1.0 · 23 November 2026

This repository accompanies Paper II. The [official series repository](https://github.com/jtraverso/split-clique-partition-gap) also hosts Part I. The English manuscript is the edition of record. The first paper, [*Nearly Quadratic Additive Gaps for Edge-Clique Partitions of Split Graphs*](https://github.com/jtraverso/split-clique-partition-gap), established the exact transfer. A proper assignment missing $L$ required pairs determines the unrestricted partition gap to within $2L$ of the residual packing gap. The coefficient two is attained by a single crossing-edge deletion on eighteen vertices. For the padded witnesses from Part I, a same-order construction tolerates quadratically many deletions within per-vertex budgets while retaining exactly the original gap when the old assigned triangles survive.

| | English | Español |
|---|---|---|
| Manuscript | [PDF](preprints/SPLITGAPII/01_manuscript/split-gap-ii-en.pdf) · [Markdown](preprints/SPLITGAPII/01_manuscript/split-gap-ii-en.md) | [PDF](preprints/SPLITGAPII/01_manuscript/split-gap-ii-es.pdf) · [Markdown](preprints/SPLITGAPII/01_manuscript/split-gap-ii-es.md) |
| Step-by-step proof ledger | [PDF](preprints/SPLITGAPII/06_proof_ledger/ledger-en.pdf) · [Markdown](preprints/SPLITGAPII/06_proof_ledger/ledger-en.md) | [PDF](preprints/SPLITGAPII/06_proof_ledger/ledger-es.pdf) · [Markdown](preprints/SPLITGAPII/06_proof_ledger/ledger-es.md) |
| Formalization companion | [PDF](preprints/SPLITGAPII/05_formalization/companion-en.pdf) | [PDF](preprints/SPLITGAPII/05_formalization/companion-es.pdf) |

**Reserved DOI** <https://doi.org/10.5281/zenodo.24452724> · [Complete edition](archives/split-gap-ii-preprint-v1.0.zip) · [Lean source archive](preprints/SPLITGAPII/05_formalization/split-gap-ii-lean-v1.0.zip)

Run `python scripts/verify_preprint.py` from the repository root to verify the edition, archive, finite examples and recorded audit. The [audit report](preprints/SPLITGAPII/02_validation/v1.0/AUDIT_RESULT.json) states the scope of the checks.

### Reproducing the Lean results

With Git and elan installed, run the following from the root of this repository. The initial checkout of the pinned dependencies and download of the Mathlib cache require network access.

```sh
cd lean
lake exe cache get
lake build SplitGapII SplitGapIIAudit
lake env lean SplitGapIIAudit.lean
lake env lean AllAxioms.lean
lake env lean SplitGapII11.lean
```

The [toolchain](lean/lean-toolchain) selects Lean 4.35.0-rc3. The [Lake manifest](lean/lake-manifest.json) pins Mathlib at `c55e6e786f49471c72fbddbec5415808896aec1e` and locks its transitive dependencies. The [provenance file](lean/PROVENANCE.json) records the revisions of Parts I, V and VI and the local adaptation of the integral lower bound. All project Lean sources are included. The [formal build record](preprints/SPLITGAPII/02_validation/v1.0/lean/status.json) and [axiom output](preprints/SPLITGAPII/02_validation/v1.0/lean/edition11-axioms.log) accompany the [audit entry point](lean/SplitGapIIAudit.lean).

### Where to check each claim

The Lean declarations below are in the namespace `QuadraticExteriorPalomar`.

| Manuscript result | Reproducible evidence |
|---|---|
| Exact transfer and two-sided partial transfer (1) | `gap_eq_residual_difference`, `gap_stability_of_partial_assignment` |
| Bounds using the loads of the chosen optimal packings (5) | `gap_stability_of_residual_loads` |
| Crossing deletions (6) and changes to the residual (7) | `gap_stability_after_cross_deletions`, `residual_gap_edit_bound` |
| Matching numbers at successive deficiency levels (8) | `gap_stability_of_marked_lists` proves the complete-core threshold. Section 4 proves the extension to any list-colorability threshold for the required graph. |
| Endpoint excess (10) | `assignment_of_vertex_budgets` constructs the assignment, and `series_gap_le_of_vertex_excess` proves the bound on the unrestricted gap. The numerical specialization follows by summing the excesses. |
| Independent matching selections (11) | `gap_of_matching_mixtures` starts from finite decompositions into matchings. `miss_product_le_exp` gives the exponential inequality. Section 5 uses Edmonds' theorem to obtain the decompositions from polytope membership. |
| Twelve-vertex example | Run the exact finite verifier below. The proof of replication for arbitrary numbers of copies is in Section 3. |
| Asymptotic estimates and conditional hypergraph recovery | Written proofs in Sections 3, 5 and 6. |

### Exact sharpness and protected assignments

Proposition 5a includes an exact computational certificate for the eighteen-vertex graph. Proposition 6a gives a written construction using bipartite list edge-coloring and a second, disjoint assignment inside the padding set. The new Lean file checks the list-size inequalities and the resulting arithmetic of the sharp example. The full arguments appear in the bilingual manuscripts.

Run the following programs from the repository root using Python 3.10 or newer.

~~~sh
python preprints/SPLITGAPII/03_reproducibility/eight_core.py
python preprints/SPLITGAPII/03_reproducibility/six_core.py
~~~

The formal source ZIP is byte-for-byte identical to the freeze checked at commit cdd5a2a. Its base library retains package version 0.2.0. Earlier private review versions and their audits remain in Git history.

The active edition is under preprints/SPLITGAPII. The directory preprints/SPLITGAPII-v1.1 preserves an earlier private review snapshot.
