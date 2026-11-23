# Additive Gaps for Edge-Clique Partitions of Split Graphs II

**Stability of Host Transfer** · Juan Pablo Traverso Gianini · Review draft 0.2

The [English manuscript](split-gap-ii-en-v0.2.md) studies how an incomplete host assignment affects the integral–fractional edge-clique partition gap of a split graph. The [first paper](https://github.com/jtraverso/split-clique-partition-gap) gives the exact transfer for complete assignments. The [previous draft](split-gap-ii-en-v0.1.md) is retained for comparison.

### Reproducing the Lean results

With Git and elan installed, run the following from the root of this repository. The initial checkout of the pinned dependencies and download of the Mathlib cache require network access.

```sh
cd lean
lake exe cache get
lake build SplitGapII SplitGapIIAudit
lake env lean SplitGapIIAudit.lean
```

The [toolchain](lean/lean-toolchain) selects Lean 4.35.0-rc3. The [Lake manifest](lean/lake-manifest.json) pins Mathlib at `c55e6e786f49471c72fbddbec5415808896aec1e` and locks its transitive dependencies. The [provenance file](lean/PROVENANCE.json) records the revisions of Parts I, V and VI and the local adaptation of the integral lower bound. All project Lean sources are included. The [build record](lean/BUILD.txt) and [axiom output](lean/AXIOMS.txt) accompany the [audit entry point](lean/SplitGapIIAudit.lean).

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

### Reproducing the twelve-vertex example

From the repository root, run `python examples/six_core.py` (Python 3, standard library). The [verifier](examples/six_core.py) computes each integral optimum by exact recursion and checks the fractional packing and dual prices over every core subset. The three pairs of partition numbers, in deletion order, are (10, 10), (11, 10) and (11, 11).
