module

public import QuadraticExteriorPalomar.InducedGap
public import GapExtremal.Bridge

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Keep the host labels and isolate each host in K. -/
def dropPalettes (N : H → Finset V) (K : Finset H) (h : H) : Finset V :=
  if h ∈ K then ∅ else N h

/-- Losing hosts costs at most their actual number of incidences, in either
direction, for the unrestricted integral-minus-fractional gap. -/
theorem gap_change_of_dropped_hosts (N : H → Finset V) (K : Finset H) :
    |gap (hostGraph N) - gap (hostGraph (dropPalettes N K))| ≤
      ((∑ h ∈ K, (N h).card : ℕ) : ℝ) := by
  classical
  let W : Finset (V ⊕ H) := (univ : Finset V).disjSum (univ \ K)
  have hi (u v : V ⊕ H) : (hostGraph (dropPalettes N K)).Adj u v ↔
      (hostGraph N).Adj u v ∧ u ∈ W ∧ v ∈ W := by
    cases u <;> cases v <;> simp [hostGraph, dropPalettes, W] <;> split_ifs <;> simp_all
  have hbound := gap_change_le_removed_edges W hi
  let edge (hv : Sigma (fun _ : H => V)) : Sym2 (V ⊕ H) := s(Sum.inl hv.2, Sum.inr hv.1)
  have hsub : (hostGraph N).edgeFinset \ (hostGraph (dropPalettes N K)).edgeFinset ⊆
      (K.sigma N).image edge := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨hp, hn⟩ := mem_sdiff.mp he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hp hn
      cases u with
      | inl a =>
        cases v with
        | inl b => exact (hn hp).elim
        | inr h =>
          have hk : h ∈ K := by
            by_contra h'
            exact hn (by simpa [dropPalettes, h'] using hp)
          exact mem_image.mpr ⟨⟨h,a⟩, mem_sigma.mpr ⟨hk, hp⟩, rfl⟩
      | inr h =>
        cases v with
        | inl a =>
          have hk : h ∈ K := by
            by_contra h'
            exact hn (by simpa [dropPalettes, h'] using hp)
          exact mem_image.mpr ⟨⟨h,a⟩, mem_sigma.mpr ⟨hk, hp⟩, Sym2.eq_swap⟩
        | inr h' => exact hp.elim
  apply hbound.trans
  exact_mod_cast ((card_le_card hsub).trans card_image_le).trans_eq (card_sigma K N)

/-- Transport a concrete fractional score and integral certificate from the
first paper after the auxiliary hosts have been isolated. -/
theorem partial_host_score_lower {B : SimpleGraph V} [DecidableRel B.Adj]
    {N : H → Finset V} {φ : V → V → H} (hh : HostHyp B N φ)
    (I : ℤ) (hI : ∀ P : Finset (Finset V), IsPack P → ∑ Q ∈ P, w B Q ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) (K : Finset H) :
    (∑ Q, y Q * w B Q) - I - ((∑ h ∈ K, (N h).card : ℕ) : ℝ) ≤
      gap (hostGraph (dropPalettes N K)) := by
  have hprev := gap_ge hh I hI hy
  have hchange := (abs_le.mp (gap_change_of_dropped_hosts N K)).2
  linarith

end QuadraticExteriorPalomar
