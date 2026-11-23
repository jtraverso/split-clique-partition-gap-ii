module

public import QuadraticExteriorPalomar.PartialAssignment

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

/-- Each lost pair has its own deleted incidence. The score and the cost are
both evaluated after the indicated host lists have been trimmed. -/
theorem retained_after_cross_deletions {V H : Type*} [Fintype V] [DecidableEq V]
    [Fintype H] [DecidableEq H] (B : SimpleGraph V) [DecidableRel B.Adj]
    (N : H → Finset V)
    (host : Finset V → H)
    (hmem : ∀ p ∈ jPairs B univ, p ⊆ N (host p))
    (hmatch : ∀ p ∈ jPairs B univ, ∀ q ∈ jPairs B univ,
      host p = host q → ∀ a ∈ p, a ∈ q → p = q)
    (del : Finset (H × V)) :
    ∃ R ⊆ jPairs B univ, ∃ f : R → H,
      (∀ p : R, p.val ⊆ (N (f p)).filter (fun a => (f p,a) ∉ del)) ∧
      (∀ p q : R, f p = f q → ∀ a ∈ p.val, a ∈ q.val → p = q) ∧
      (jPairs B univ).card - R.card ≤ del.card := by
  classical
  let J := jPairs B univ
  let good (p : Finset V) := ∀ a ∈ p, (host p, a) ∉ del
  let R := J.filter good
  have hsub : R ⊆ J := filter_subset _ _
  have hw (p : ↥(J \ R)) : ∃ a ∈ p.val, (host p.val, a) ∈ del := by
    have h := mem_sdiff.mp p.property
    have hn : ¬ good p.val := fun hg => h.2 (mem_filter.mpr ⟨h.1, hg⟩)
    simpa [good] using hn
  choose a ha hdel using hw
  let hit (p : ↥(J \ R)) : del := ⟨(host p.val, a p), hdel p⟩
  have hinj : Function.Injective hit := by
    intro p q heq
    have hpair := congrArg Subtype.val heq
    have he : host p.val = host q.val := congrArg Prod.fst hpair
    have hv : a p = a q := congrArg Prod.snd hpair
    exact Subtype.ext (hmatch _ (mem_sdiff.mp p.property).1 _ (mem_sdiff.mp q.property).1
      he _ (ha p) (hv ▸ ha q))
  have hcount : J.card - R.card ≤ del.card := by
    simpa only [Fintype.card_coe, card_sdiff_of_subset hsub] using Fintype.card_le_of_injective hit hinj
  exact ⟨R, hsub, fun p => host p.val,
    fun p v hv => mem_filter.mpr ⟨hmem _ (hsub p.property) hv, (mem_filter.mp p.property).2 v hv⟩,
    fun p q he a hp hq => Subtype.ext (hmatch _ (hsub p.property) _ (hsub q.property) he a hp hq),
    hcount⟩

/-- Transport a fractional score lower bound through arbitrary deletions of crossing incidences. -/
theorem gap_ge_after_cross_deletions {V H : Type*} [Fintype V] [DecidableEq V]
    [Fintype H] [DecidableEq H] (B : SimpleGraph V) [DecidableRel B.Adj]
    (N : H → Finset V) (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (host : Finset V → H)
    (hmem : ∀ p ∈ jPairs B univ, p ⊆ N (host p))
    (hmatch : ∀ p ∈ jPairs B univ, ∀ q ∈ jPairs B univ,
      host p = host q → ∀ a ∈ p, a ∈ q → p = q)
    (I : ℤ) (hI : ∀ P : Finset (Finset V), IsPack P → ∑ Q ∈ P, w B Q ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) (del : Finset (H × V)) :
    (∑ Q, y Q * w B Q) - I - 2 * (del.card : ℝ) ≤
      gap (hostGraph (Sum.elim (fun h => (N h).filter fun a => (h,a) ∉ del)
        (fun _ : Finset V => ∅))) := by
  obtain ⟨R,hsub,f,hf,hm,hl⟩ := retained_after_cross_deletions B N host hmem hmatch del
  have h := gap_ge_of_partial_assignment B (fun h => (N h).filter fun a => (h,a) ∉ del)
    (fun h a ha b hb => hi h a (mem_filter.mp ha).1 b (mem_filter.mp hb).1)
    R hsub f hf hm I hI hy
  exact le_trans (sub_le_sub_left (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hl) (by norm_num)) _) h

end QuadraticExteriorPalomar
