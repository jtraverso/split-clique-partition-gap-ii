# Stability of the Clique Partition Gap in Split Graphs

Juan Pablo Traverso Gianini Â· Split Gap II Â· Preprint 1.0

This branch presents three statements from the [published preprint](https://doi.org/10.5281/zenodo.24452724) for comparison by the Palomar Registry. The [publication archive](https://github.com/jtraverso/split-clique-partition-gap-ii/tree/3e009f6f9a0103363b1714e1583f12a0a731441b) contains the bilingual manuscripts, proof ledgers, finite certificates and full Lean source.

| Paper | Lean statement in `SplitGapIIRegistry` |
| --- | --- |
| Theorem 1. Bilateral stability of a partial host assignment | `gap_stability_of_partial_assignment` |
| Corollary 5. Perturbation by crossing-edge deletions | `gap_stability_after_cross_deletions` |
| Corollary 8, equation (10). Endpoint excess with at least twice as many hosts as core vertices | `series_gap_le_of_vertex_excess` |

Theorem 1 compares the gap in the original split graph with the difference of residual optima. Its error bound is twice the number of unassigned required pairs. The comparator tests these three statements. The sharpness example and the protected padding construction are documented separately in the publication archive.

## Reproduction

Use the toolchain in `lean-toolchain` and the dependency revisions in `lake-manifest.json`.

```sh
lake exe cache get
lake build Challenge Solution
```

`Challenge.lean` gives the definitions and three statement placeholders. `Solution.lean` proves the same statements using the published sources. Its auxiliary lemma identifies the supremum of the integral scores with the score of an optimal packing. The imported proof modules are copied from the published Lean tree. `PROVENANCE.json` reproduces the provenance of the full upstream freeze, including modules outside the three statements.
