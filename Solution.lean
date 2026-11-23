module

public import QuadraticExteriorPalomar.ExactTransfer
public import QuadraticExteriorPalomar.SeriesGap

@[expose] public section

namespace SplitGapIIRegistry
open GapExtremal QuadraticExteriorPalomar Finset
open scoped BigOperators
variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Best total score of an integral family with disjoint pairs. -/
noncomputable def integralScore (B : SimpleGraph V) [DecidableRel B.Adj] : ℤ :=
  sSup {s : ℤ | ∃ P : Finset (Finset V), IsPack P ∧ (∀ Q ∈ P, 2 ≤ Q.card) ∧ ∑ Q ∈ P, w B Q = s}

private theorem integralScore_eq (B : SimpleGraph V) [DecidableRel B.Adj] :
    integralScore B = residualInt B := by
  obtain ⟨hp, hs, hm⟩ := (exists_best_pack B).choose_spec
  apply IsGreatest.csSup_eq
  exact ⟨⟨_, hp, hs, rfl⟩, fun z ⟨T, hT, _, hz⟩ => hz ▸ hm T hT⟩

/-- The two gaps differ by at most twice the number of unassigned required pairs. -/
theorem gap_stability_of_partial_assignment
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (J₀ : Finset (Finset V)) (hsub : J₀ ⊆ jPairs B univ) (host : J₀ → H)
    (hmem : ∀ p : J₀, p.val ⊆ N (host p))
    (hmatch : ∀ p q : J₀, host p = host q → ∀ a ∈ p.val, a ∈ q.val → p = q) :
    |gap (hostGraph N) -
      (residualSup B - integralScore B)| ≤ 2 * (((jPairs B univ).card - J₀.card : ℕ) : ℝ) := by
  rw [integralScore_eq]
  exact QuadraticExteriorPalomar.gap_stability_of_partial_assignment B N hi J₀ hsub host hmem hmatch

/-- Deleting crossing incidences from a complete assignment changes the gap by at most twice their number. -/
theorem gap_stability_after_cross_deletions
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (host : Finset V → H) (hmem : ∀ p ∈ jPairs B univ, p ⊆ N (host p))
    (hmatch : ∀ p ∈ jPairs B univ, ∀ q ∈ jPairs B univ,
      host p = host q → ∀ a ∈ p, a ∈ q → p = q) (del : Finset (H × V)) :
    |gap (hostGraph (fun h => (N h).filter fun a => (h,a) ∉ del)) - gap (hostGraph N)| ≤
      2 * (del.card : ℝ) := by
  exact QuadraticExteriorPalomar.gap_stability_after_cross_deletions B N hi host hmem hmatch del

/-- With at least twice as many hosts as core vertices, only omissions beyond half the core size at each endpoint contribute to this upper bound. -/
theorem series_gap_le_of_vertex_excess (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V)) (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (s : C → ℕ) (hsize : 2 * C.card ≤ Cᶜ.card)
    (hmiss : ∀ a : C, (Cᶜ.filter (fun x => ¬ G.Adj x a.val)).card ≤ C.card / 2 + s a) :
    GapExtremal.gap G ≤ 2 * (↑(∑ a, s a) : ℝ) := by
  exact QuadraticExteriorPalomar.series_gap_le_of_vertex_excess G C hC hI s hsize hmiss

end SplitGapIIRegistry
