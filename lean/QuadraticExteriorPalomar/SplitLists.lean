module

public import PaperVIVendor.HaggkvistJanssen

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset
open scoped BigOperators

/-- A family of core bases in which any two distinct bases have disjoint endpoints. -/
def BasesMatching {Core : Type*}
    (F : Finset (⊤ : SimpleGraph Core).edgeSet) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, e ≠ f → ¬ ∃ v, v ∈ e.val ∧ v ∈ f.val

/-- Pad each list only up to the required size. The auxiliary color of
index `t` can occur only on a matching of bases whose deficit exceeds `t`. -/
theorem partial_host_assignment_of_deficit_bounds {Core Host : Type*} [Fintype Core] [DecidableEq Core]
    (lists : (⊤ : SimpleGraph Core).edgeSet → Finset Host) (cap : ℕ → ℕ)
    (hcap : ∀ t < Fintype.card Core, ∀ F : Finset (⊤ : SimpleGraph Core).edgeSet,
      (∀ e ∈ F, t < Fintype.card Core - (lists e).card) →
      BasesMatching F → F.card ≤ cap t) :
    ∃ S : Finset (⊤ : SimpleGraph Core).edgeSet, ∃ host : S → Host,
      (∀ e, host e ∈ lists e.1) ∧
      (∀ e f v, v ∈ e.1.val → v ∈ f.1.val → host e = host f → e = f) ∧
      Fintype.card (⊤ : SimpleGraph Core).edgeSet ≤ S.card + ∑ t ∈ range (Fintype.card Core), cap t := by
  classical
  let E := (⊤ : SimpleGraph Core).edgeSet
  let c := Fintype.card Core
  let deficit (e : E) := c - (lists e).card
  let full (e : E) : Finset (Host ⊕ ℕ) :=
    (lists e).image Sum.inl ∪ (range (deficit e)).image Sum.inr
  have hfull (e : E) : c ≤ (full e).card := by
    have hd : Disjoint ((lists e).image (Sum.inl : Host → Host ⊕ ℕ))
        ((range (deficit e)).image (Sum.inr : ℕ → Host ⊕ ℕ)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨a, _, rfl⟩ := mem_image.mp hx
      obtain ⟨t, _, h⟩ := mem_image.mp hy
      cases h
    rw [show full e = _ by rfl, card_union_of_disjoint hd, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective, card_range]
    unfold deficit
    omega
  obtain ⟨colour, hcolour⟩ := HaggkvistJanssen.exists_listEdgeColoring_complete full hfull
  have hdummy (e : E) {t : ℕ} (h : colour e = Sum.inr t) : t < deficit e := by
    have he := hcolour e
    rw [h] at he
    simpa [full] using he
  let bad : Finset E := univ.filter fun e => ∃ t : ℕ, colour e = Sum.inr t
  let S := univ \ bad
  let F (t : ℕ) : Finset E := univ.filter fun e => colour e = Sum.inr t
  have hF (t : ℕ) (ht : t ∈ range c) : (F t).card ≤ cap t := by
    refine hcap t (mem_range.mp ht) (F t) (fun e he => hdummy e (mem_filter.mp he).2) ?_
    intro e he f hf hne
    rintro ⟨v, hv, hv'⟩
    have heq := (mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm
    exact colour.valid (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, v, hv, hv'⟩) heq
  have hsub : bad ⊆ (range c).biUnion F := by
    intro e he
    obtain ⟨t, ht⟩ := (mem_filter.mp he).2
    have hlt := hdummy e ht
    have hdc : deficit e ≤ c := Nat.sub_le _ _
    exact mem_biUnion.mpr ⟨t, mem_range.mpr (hlt.trans_le hdc), mem_filter.mpr ⟨mem_univ _, ht⟩⟩
  have hbad : bad.card ≤ ∑ t ∈ range c, cap t := by
    calc
      bad.card ≤ ((range c).biUnion F).card := card_le_card hsub
      _ ≤ ∑ t ∈ range c, (F t).card := card_biUnion_le
      _ ≤ ∑ t ∈ range c, cap t := sum_le_sum hF
  have hreal (e : S) : ∃ x ∈ lists e.1, colour e.1 = Sum.inl x := by
    have hm := hcolour e.1
    cases he : colour e.1 with
    | inl x =>
      rw [he] at hm
      exact ⟨x, by simpa [full] using hm, rfl⟩
    | inr t =>
      exact False.elim ((mem_sdiff.mp e.2).2
        (mem_filter.mpr ⟨mem_univ _, t, he⟩))
  choose host hmem hhost using hreal
  refine ⟨S, host, hmem, ?_, ?_⟩
  · intro e f v he hf hh
    apply Subtype.ext
    by_contra hne
    exact colour.valid (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, v, he, hf⟩)
      ((hhost e).trans (by rw [hh, ← hhost f]))
  · have he : S.card + bad.card = Fintype.card E := by
      rw [← card_univ]
      exact card_sdiff_add_card_eq_card (subset_univ _)
    change Fintype.card E ≤ S.card + ∑ t ∈ range c, cap t
    omega

/-- Each auxiliary color is owned by one endpoint. Its color class in a
proper coloring contains at most one edge. -/
theorem assignment_of_vertex_budgets {C H : Type*} [Fintype C] [DecidableEq C] [DecidableEq H]
    (lists : (⊤ : SimpleGraph C).edgeSet → Finset H) (s : C → ℕ)
    (budget : ∀ e, Fintype.card C ≤ (lists e).card + ∑ u ∈ e.val.toFinset, s u) :
    ∃ R : Finset (⊤ : SimpleGraph C).edgeSet, ∃ host : R → H,
      (∀ e, host e ∈ lists e.1) ∧
      (∀ e f u, u ∈ e.1.val → u ∈ f.1.val → host e = host f → e = f) ∧
      Fintype.card (⊤ : SimpleGraph C).edgeSet ≤ R.card + ∑ u, s u := by
  classical
  let E := (⊤ : SimpleGraph C).edgeSet
  let A := (u : C) × Fin (s u)
  let aux (e : E) : Finset A := e.val.toFinset.sigma fun u => (univ : Finset (Fin (s u)))
  let full (e : E) : Finset (H ⊕ A) := (lists e).disjSum (aux e)
  have hfull (e : E) : Fintype.card C ≤ (full e).card := by
    change _ ≤ ((lists e).disjSum (e.val.toFinset.sigma fun u => (univ : Finset (Fin (s u))))).card
    rw [Finset.card_disjSum, Finset.card_sigma]
    simpa using budget e
  obtain ⟨col,hcol⟩ := HaggkvistJanssen.exists_listEdgeColoring_complete full hfull
  let bad : Finset E := univ.filter fun e => ∃ a : A, col e = Sum.inr a
  have haux (e : bad) : ∃ a : A, col e.val = Sum.inr a := (mem_filter.mp e.2).2
  choose tag htag using haux
  have incident (e : bad) : (tag e).1 ∈ e.val.val := by
    have hm := hcol e.val
    rw [htag e] at hm
    exact Sym2.mem_toFinset.mp (mem_sigma.mp (inr_mem_disjSum.mp hm)).1
  have inj : Function.Injective tag := by
    intro e f he
    apply Subtype.ext
    by_contra hne
    exact col.valid (SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨hne,(tag e).1,incident e,he.symm ▸ incident f⟩)
      ((htag e).trans (by rw [he, ← htag f]))
  have hb : bad.card ≤ ∑ u, s u := by
    simpa [A,Fintype.card_sigma] using Fintype.card_le_of_injective tag inj
  let R := univ \ bad
  have real (e : R) : ∃ h ∈ lists e.val, col e.val = Sum.inl h := by
    have hm := hcol e.val
    cases hc : col e.val with
    | inl h => exact ⟨h,inl_mem_disjSum.mp (hc ▸ hm),rfl⟩
    | inr a => exact False.elim ((mem_sdiff.mp e.2).2 (mem_filter.mpr ⟨mem_univ _,a,hc⟩))
  choose host hmem hhost using real
  refine ⟨R,host,hmem,?_,?_⟩
  · intro e f u he hf hh
    apply Subtype.ext
    by_contra hne
    exact col.valid (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne,u,he,hf⟩)
      ((hhost e).trans (by rw [hh, ← hhost f]))
  · have ht : R.card + bad.card = Fintype.card E := by
      rw [← card_univ]; exact card_sdiff_add_card_eq_card (subset_univ _)
    change Fintype.card E ≤ R.card + ∑ u, s u
    omega

/-- A port cover certifies an upper bound for a matching of deficient bases. -/
theorem matching_card_le_port_cover {Core : Type*} [DecidableEq Core]
    (F : Finset (⊤ : SimpleGraph Core).edgeSet) (ports : Finset Core)
    (hm : BasesMatching F) (hcover : ∀ e ∈ F, ∃ v ∈ ports, v ∈ e.val) :
    F.card ≤ ports.card := by
  classical
  have hex (e : F) : ∃ v ∈ ports, v ∈ e.1.val := hcover e.1 e.2
  choose hit hports hend using hex
  have hinj : Function.Injective hit := by
    intro e f h
    apply Subtype.ext
    by_contra hne
    exact hm e.1 e.2 f.1 f.2 hne ⟨hit e, hend e, h.symm ▸ hend f⟩
  rw [← show F.attach.card = F.card by simp, ← card_image_of_injective _ hinj]
  exact card_le_card (fun v hv => by
    obtain ⟨e, _, rfl⟩ := mem_image.mp hv
    exact hports e)

theorem matching_card_le_half_core {Core : Type*} [Fintype Core] [DecidableEq Core]
    (F : Finset (⊤ : SimpleGraph Core).edgeSet) (hm : BasesMatching F) :
    F.card ≤ Fintype.card Core / 2 := by
  classical
  have hd : (↑F : Set (⊤ : SimpleGraph Core).edgeSet).PairwiseDisjoint
      (fun e => e.val.toFinset) := by
    intro e he f hf hef
    change Disjoint e.val.toFinset f.val.toFinset
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact hm e he f hf hef ⟨v, Sym2.mem_toFinset.mp hv, Sym2.mem_toFinset.mp hv'⟩
  have hc := (F.biUnion fun e => e.val.toFinset).card_le_univ
  rw [card_biUnion hd, sum_congr rfl (g := fun _ => 2) (fun e _ =>
    Sym2.card_toFinset_of_not_isDiag _
      ((⊤ : SimpleGraph Core).not_isDiag_of_mem_edgeSet e.2))] at hc
  simp at hc
  omega

end QuadraticExteriorPalomar
