# Lean companion to Stability of Host Transfer

## What the formal statement says

Preprint 1.0 uses the unrestricted integral and fractional edge-clique partition numbers from Part I. The Lean development proves the two-sided estimate (1) of Theorem 1 on the original split graph. Its input includes a residual graph, independent host neighborhoods and a proper partial assignment on actual core pairs. The parameter counting missed pairs is the cardinality of the complement of this assignment.

Lemma 4 charges the two directions separately to the unused capacities of optimal residual packings. Corollary 5 permits arbitrary crossing-edge deletions from a complete assignment, including deletions which isolate hosts. Proposition 6 bounds the change in the residual packing gap under edits on a fixed core. In Proposition 7 the compiled list bound takes the complete-core threshold. Corollary 8 bounds the unrestricted gap by twice the sum of endpoint excesses. In Theorem 9 the formal argument starts with finite convex decompositions into legal matchings and proves the unweighted product estimate and its exponential comparison. Edmonds' polytope characterization supplies those decompositions in the manuscript.

## Reproducing the checks

The official repository is <https://github.com/jtraverso/split-clique-partition-gap-ii>. Its README maps these statements to Lean declarations. The source archive distributed beside this companion contains the package under the directory `lean`. Within that directory run the following commands using elan. First-time installation requires network access.

```sh
lake exe cache get
lake build SplitGapII SplitGapIIAudit
lake env lean SplitGapIIAudit.lean
lake env lean AllAxioms.lean
```

The package pins Lean 4.35.0-rc3 and the Mathlib revision in its Lake manifest. The first audit prints the axiom dependencies of 25 named declarations. The second scans the imported project modules and rejects any theorem using axioms outside propositional extensionality, classical choice and quotient soundness. The validation directory records the clean build and the exhaustive list.

The middle row of the twelve-vertex example also has a finite verifier. From the repository root, run `python examples/six_core.py`. It checks the dual prices, the fractional packings, the obstruction to an integral optimum of six and the three exact integral optima using Python's standard library.

The general list threshold, the replication argument and the asymptotic statements, including Proposition 10, have written proofs in the manuscript. The two audits certify the formal statements indicated above.
