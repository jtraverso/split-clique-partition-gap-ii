module

import all GapExtremal.Bridge
import all GapExtremal.Completion
import all GapExtremal.Defs
import all GapExtremal.Global
import all GapExtremal.GlobalLemmas
import all GapExtremal.Residual
import all GraphBase.Clique.CliqueSets
import all GraphBase.Clique.Partition
import all PaperV.ConflictGraph
import all PaperV.Core
import all PaperV.HostRealizer
import all PaperV.RealizabilityDefect
import all PaperV.Realizer
import all PaperV.UnitBoundaryCompletion
import all PaperV.UnitBoundaryWitnesses
import all PaperV.WeightedTransfer
import all PaperVI.Counting
import all PaperVI.Defs
import all PaperVIVendor.HaggkvistJanssen
import all PaperVIVendor.ListEdgeColoringComplete
import all PaperVIVendor.ListEdgeColoringComplete.Basic
import all PaperVIVendor.ListEdgeColoringComplete.Certificate
import all PaperVIVendor.ListEdgeColoringComplete.Main
import all PaperVIVendor.ListEdgeColoringComplete.Polynomial
import all QuadraticExteriorPalomar.CrossDeletions
import all QuadraticExteriorPalomar.ExactTransfer
import all QuadraticExteriorPalomar.HostTransfer
import all QuadraticExteriorPalomar.InducedGap
import all QuadraticExteriorPalomar.IntegralRealization
import all QuadraticExteriorPalomar.IsolatedLabels
import all QuadraticExteriorPalomar.MarkedLists
import all QuadraticExteriorPalomar.PartialAssignment
import all QuadraticExteriorPalomar.Recovery
import all QuadraticExteriorPalomar.Redundancy
import all QuadraticExteriorPalomar.ResidualProjection
import all QuadraticExteriorPalomar.Retention
import all QuadraticExteriorPalomar.SeriesGap
import all QuadraticExteriorPalomar.SplitBound
import all QuadraticExteriorPalomar.SplitCost
import all QuadraticExteriorPalomar.SplitLists
import all QuadraticExteriorPalomar.SplitRealizer
import all QuadraticExteriorPalomar.WeightedRecovery
import all SplitGapII
import all SplitGapIIAudit
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut rows := #[]
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    unless [`GapExtremal, `GraphBase, `PaperV, `PaperVI, `PaperVIVendor, `QuadraticExteriorPalomar, `SplitGapII, `SplitGapIIAudit].any (·.isPrefixOf modName) do continue
    for info in env.header.moduleData[idx]!.constants do
      unless info matches .thmInfo _ do continue
      let name := info.name
      let axioms ← collectAxioms name
      unless axioms.all ([`propext, `Classical.choice, `Quot.sound].contains ·) do
        throwError "Unexpected axioms for {name}: {axioms}"
      rows := rows.push s!"{modName}\t{name}\t{axioms}"
  unless rows.any (·.contains "QuadraticExteriorPalomar.gap_stability_of_residual_loads\t") do throwError "Missing mixed endpoint"
  if rows.isEmpty then throwError "No project theorems found"
  for row in rows.qsort (· < ·) do IO.println row
  IO.println s!"PASS: {rows.size} project theorems"
