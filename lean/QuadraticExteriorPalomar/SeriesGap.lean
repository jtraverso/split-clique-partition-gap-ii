module

public import QuadraticExteriorPalomar.SplitBound
public import GapExtremal.Defs

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Identify the unrestricted integral optimum in the two papers' libraries. -/
theorem cp_eq_series_cp (G : SimpleGraph V) :
    PaperVI.cp G = G.cliquePartitionNumber := by
  apply le_antisymm
  · obtain ⟨P, h, hc⟩ := SimpleGraph.exists_isCliquePartition_card_eq G
    rw [← hc]
    exact PaperVI.cp_le ⟨h.two_le, h.isClique, h.existsUnique⟩
  · obtain ⟨P, h, hc⟩ := PaperVI.exists_cp G
    rw [← hc]
    exact SimpleGraph.cliquePartitionNumber_le ⟨h.two_le, h.isClique, h.existsUnique⟩

private theorem edge_load (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : Finset V → ℝ} (hw : G.IsFracCliquePartition w) :
    ∀ e ∈ G.edgeFinset, ∑ Q : Finset V, (if e.toFinset ⊆ Q then w Q else 0) = 1 := by
  intro e
  induction e using Sym2.ind with
  | h a b =>
    intro h
    have hab : G.Adj a b := SimpleGraph.mem_edgeFinset.mp h
    simpa [Finset.sum_filter, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using hw.edge a b hab

private theorem series_gap_of_cost_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ℝ) (h : ∀ w, G.IsFracCliquePartition w → (PaperVI.cpLe 3 G : ℝ) ≤ (∑ Q, w Q) + L) :
    GapExtremal.gap G ≤ L := by
  have hf : (PaperVI.cpLe 3 G : ℝ) - L ≤ G.fracCliquePartitionNumber :=
    SimpleGraph.le_fracCliquePartitionNumber fun w hw => by linarith [h w hw]
  have hi : (G.cliquePartitionNumber : ℝ) ≤ PaperVI.cpLe 3 G := by
    rw [← cp_eq_series_cp]
    exact_mod_cast PaperVI.cp_le_cpLe G (by decide : 2 ≤ 3)
  unfold GapExtremal.gap
  linarith

/-- The list-deficit estimate for exactly the gap defined in Part I. -/
theorem series_gap_le_of_deficit_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V))
    (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y) (cap : ℕ → ℕ)
    (hc : ∀ t < C.card, ∀ F : Finset (⊤ : SimpleGraph C).edgeSet,
      (∀ e ∈ F, t < C.card - (splitLists G C e).card) → BasesMatching F → F.card ≤ cap t) :
    GapExtremal.gap G ≤ 2 * (↑(∑ t ∈ range C.card, cap t) : ℝ) := by
  apply series_gap_of_cost_bound
  intro w hw
  exact split_fractional_gap_of_deficit_bounds G C hC hI cap hc w hw.nonneg
    (fun Q hQ => (hw.support Q hQ).2) (edge_load G hw)

/-- The linear family measured with Part I's unrestricted fractional infimum. -/
theorem series_gap_le_of_sparse_exceptions (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V)) (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (ports : Finset C) (r : ℕ) (hr : ports.card ≤ r) (hr₂ : r * r ≤ C.card)
    (hsize : 2 * C.card ≤ Cᶜ.card)
    (hmiss : ∀ a : C, (Cᶜ.filter (fun x => ¬ G.Adj x a.val)).card ≤
      C.card / 2 + if a ∈ ports then r else 0) :
    GapExtremal.gap G ≤ 4 * (C.card : ℝ) := by
  apply series_gap_of_cost_bound
  intro w hw
  exact split_fractional_gap_of_sparse_exceptions G C hC hI ports r hr hr₂ hsize hmiss
    w hw.nonneg (fun Q hQ => (hw.support Q hQ).2) (edge_load G hw)

/-- Endpoint-owned colors charge each excess omission just once. -/
theorem series_gap_le_of_vertex_excess (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V)) (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (s : C → ℕ) (hsize : 2 * C.card ≤ Cᶜ.card)
    (hmiss : ∀ a : C, (Cᶜ.filter (fun x => ¬ G.Adj x a.val)).card ≤ C.card / 2 + s a) :
    GapExtremal.gap G ≤ 2 * (↑(∑ a, s a) : ℝ) := by
  classical
  have hsum (e : (⊤ : SimpleGraph C).edgeSet) :
      C.card - (splitLists G C e).card ≤
        ∑ a ∈ e.val.toFinset, (s a) := by
    let miss (a : C) := Cᶜ.filter fun x => ¬ G.Adj x a.val
    let B := e.val.toFinset
    have hB : B.card = 2 := Sym2.card_toFinset_of_not_isDiag _
      ((⊤ : SimpleGraph C).not_isDiag_of_mem_edgeSet e.2)
    have hsub : Cᶜ ⊆ splitLists G C e ∪ B.biUnion miss := by
      intro x hx
      by_cases h : ∀ a ∈ B, G.Adj x a.val
      · exact mem_union_left _ (mem_filter.mpr ⟨hx, h⟩)
      · push_neg at h
        obtain ⟨a, ha, hxa⟩ := h
        exact mem_union_right _ (mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨hx, hxa⟩⟩)
    have hcount : Cᶜ.card ≤ (splitLists G C e).card + (B.biUnion miss).card :=
      (card_le_card hsub).trans (card_union_le _ _)
    have hmiss' : (B.biUnion miss).card ≤ 2 * (C.card / 2) +
        ∑ a ∈ B, (s a) := by
      calc
        _ ≤ ∑ a ∈ B, (miss a).card := card_biUnion_le
        _ ≤ ∑ a ∈ B, (C.card / 2 + s a) :=
          sum_le_sum fun a _ => hmiss a
        _ = _ := by rw [sum_add_distrib]; simp [hB]
    change C.card - (splitLists G C e).card ≤ ∑ a ∈ B, (s a)
    omega
  obtain ⟨R,host,hm,hp,hcard⟩ := assignment_of_vertex_budgets (splitLists G C) s (by
    intro e
    rw [Fintype.card_coe]
    have := hsum e
    omega)
  have hi := split_cpLe_three_of_assignment G C hC hI _ R host hm hp hcard
  apply series_gap_of_cost_bound
  intro w hw
  have hl := split_fractional_price G C hI w hw.nonneg (fun Q h => (hw.support Q h).2)
    (edge_load G hw)
  have hc : PaperVI.uCount G C = C.card.choose 2 := PaperVI.card_innerEdges_of_isClique G C hC
  rw [hc] at hl
  have hu : (PaperVI.cpLe 3 G : ℝ) + C.card.choose 2 ≤
      (PaperVI.sCount G C : ℝ) + 2 * (↑(∑ a, s a) : ℝ) := by exact_mod_cast hi
  linarith

end QuadraticExteriorPalomar
