module

public import QuadraticExteriorPalomar.SplitLists
public import QuadraticExteriorPalomar.SplitCost

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset PaperVI
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual common exterior neighborhood of a core base. -/
def splitLists (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (e : (⊤ : SimpleGraph C).edgeSet) : Finset V :=
  Cᶜ.filter fun x => ∀ a ∈ e.val.toFinset, G.Adj x a.val

/-- Realize the retained bases as literal triangles of the split graph, and
pay the unhosted bases as individual edges. -/
theorem split_cpLe_three_of_assignment (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V))
    (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (budget : ℕ) (R : Finset (⊤ : SimpleGraph C).edgeSet) (host : R → V)
    (hmem : ∀ e, host e ∈ splitLists G C e.1)
    (hproper : ∀ e f v, v ∈ e.1.val → v ∈ f.1.val → host e = host f → e = f)
    (hR : Fintype.card (⊤ : SimpleGraph C).edgeSet ≤ R.card + budget) :
    cpLe 3 G + C.card.choose 2 ≤ sCount G C + 2 * budget := by
  classical
  let base (e : R) : Finset V := e.1.val.toFinset.image Subtype.val
  let tri (e : R) : Finset V := insert (host e) (base e)
  have hbaseC (e : R) : base e ⊆ C := by
    intro a ha
    obtain ⟨v, _, rfl⟩ := mem_image.mp ha
    exact v.2
  have hbase_mem (e : R) (v : C) (hv : v.val ∈ base e) : v ∈ e.1.val := by
    obtain ⟨w, hw, he⟩ := mem_image.mp hv
    exact (Subtype.ext he) ▸ Sym2.mem_toFinset.mp hw
  have hhost (e : R) : host e ∉ C ∧ ∀ a ∈ base e, G.Adj (host e) a := by
    have hh := mem_filter.mp (hmem e)
    refine ⟨mem_compl.mp hh.1, ?_⟩
    intro a ha
    obtain ⟨w, hw, rfl⟩ := mem_image.mp ha
    exact hh.2 w hw
  have hbase_card (e : R) : (base e).card = 2 := by
    rw [show base e = e.1.val.toFinset.image Subtype.val from rfl,
      card_image_of_injective _ Subtype.val_injective]
    exact Sym2.card_toFinset_of_not_isDiag _
      ((⊤ : SimpleGraph C).not_isDiag_of_mem_edgeSet e.1.2)
  have hinter (e : R) : tri e ∩ C = base e := by
    ext a
    constructor
    · intro ha
      rcases mem_insert.mp (mem_inter.mp ha).1 with he | he
      · exact False.elim ((hhost e).1 (he ▸ (mem_inter.mp ha).2))
      · exact he
    · intro ha
      exact mem_inter.mpr ⟨mem_insert_of_mem ha, hbaseC e ha⟩
  have htriinj : Function.Injective tri := by
    intro e f he
    have hbaseeq := (hinter e).symm.trans ((congrArg (fun Q => Q ∩ C) he).trans (hinter f))
    have hb : e.1.val.toFinset = f.1.val.toFinset :=
      Finset.image_injective Subtype.val_injective hbaseeq
    refine Subtype.ext (Subtype.ext (Sym2.ext fun v => ?_))
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hb]
  let P := R.attach.image tri
  have hp : P.card = R.card := by rw [show P = R.attach.image tri by rfl,
    card_image_of_injective _ htriinj, card_attach]
  have hR' : C.card.choose 2 ≤ R.card + budget := by
    rw [← SimpleGraph.edgeFinset_card,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe] at hR
    exact hR
  refine split_cost_of_triangle_family G C hC hI P ?_ ?_ ?_ _ (by rwa [hp])
  · intro Q hQ
    obtain ⟨e, _, rfl⟩ := mem_image.mp hQ
    rw [show tri e = insert (host e) (base e) from rfl,
      card_insert_of_notMem (fun hx => (hhost e).1 (hbaseC e hx)), hbase_card e]
  · intro Q hQ a ha d hd hne
    obtain ⟨e, _, rfl⟩ := mem_image.mp hQ
    rcases mem_insert.mp ha with rfl | ha <;> rcases mem_insert.mp hd with rfl | hd
    · exact False.elim (hne rfl)
    · exact (hhost e).2 _ hd
    · exact ((hhost e).2 _ ha).symm
    · exact hC (hbaseC e ha) (hbaseC e hd) hne
  · intro Q hQ D hD hn
    obtain ⟨e, _, rfl⟩ := mem_image.mp hQ
    obtain ⟨f, _, rfl⟩ := mem_image.mp hD
    have hcases (v : V) (he : v ∈ tri e) (hf : v ∈ tri f) :
        (v = host e ∧ v = host f) ∨ (v ∈ base e ∧ v ∈ base f) := by
      rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with hf | hf
      · exact Or.inl ⟨rfl, hf⟩
      · exact False.elim ((hhost e).1 (hbaseC f hf))
      · exact False.elim ((hhost f).1 (hf ▸ hbaseC e he))
      · exact Or.inr ⟨he, hf⟩
    rw [card_le_one]
    intro a ha b hb
    by_contra hne
    have hef : e ≠ f := fun he => hn (congrArg tri he)
    rcases hcases a (mem_inter.mp ha).1 (mem_inter.mp ha).2 with ⟨he, hf⟩ | ⟨he, hf⟩
    · rcases hcases b (mem_inter.mp hb).1 (mem_inter.mp hb).2 with ⟨he', _⟩ | ⟨he', hf'⟩
      · exact hne (he.trans he'.symm)
      · exact hef (hproper e f ⟨b, hbaseC e he'⟩ (hbase_mem e _ he') (hbase_mem f _ hf')
          (he.symm.trans hf))
    · rcases hcases b (mem_inter.mp hb).1 (mem_inter.mp hb).2 with ⟨he', hf'⟩ | ⟨he', hf'⟩
      · exact hef (hproper e f ⟨a, hbaseC e he⟩ (hbase_mem e _ he) (hbase_mem f _ hf)
          (he'.symm.trans hf'))
      · let x : C := ⟨a, hbaseC e he⟩
        let y : C := ⟨b, hbaseC e he'⟩
        have hnxy : x ≠ y := fun hh => hne (congrArg Subtype.val hh)
        have heq := (Sym2.mem_and_mem_iff hnxy).mp
          ⟨hbase_mem e x he, hbase_mem e y he'⟩
        have hfeq := (Sym2.mem_and_mem_iff hnxy).mp
          ⟨hbase_mem f x hf, hbase_mem f y hf'⟩
        exact hef (Subtype.ext (Subtype.ext (heq.trans hfeq.symm)))

/-- Realize the retained bases as literal triangles of the split graph, and
pay the unhosted bases using the deficit tiers. -/
theorem split_cpLe_three_of_deficit_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V))
    (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (cap : ℕ → ℕ)
    (hcap : ∀ t < C.card, ∀ F : Finset (⊤ : SimpleGraph C).edgeSet,
      (∀ e ∈ F, t < C.card - (splitLists G C e).card) → BasesMatching F → F.card ≤ cap t) :
    cpLe 3 G + C.card.choose 2 ≤ sCount G C + 2 * (∑ t ∈ range C.card, cap t) := by
  classical
  obtain ⟨R, host, hmem, hproper, hR⟩ :=
    partial_host_assignment_of_deficit_bounds (splitLists G C) cap
      (by simpa only [Fintype.card_coe] using hcap)
  exact split_cpLe_three_of_assignment G C hC hI _ R host hmem hproper (by simpa only [Fintype.card_coe] using hR)

/-- Compare the constructed integral solution with every feasible fractional
solution on the same split graph. -/
theorem split_fractional_gap_of_deficit_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V))
    (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (cap : ℕ → ℕ)
    (hcap : ∀ t < C.card, ∀ F : Finset (⊤ : SimpleGraph C).edgeSet,
      (∀ e ∈ F, t < C.card - (splitLists G C e).card) → BasesMatching F → F.card ≤ cap t)
    (w : Finset V → ℝ) (hnonneg : ∀ Q, 0 ≤ w Q)
    (hsupport : ∀ Q, w Q ≠ 0 → G.IsClique (Q : Set V))
    (hcover : ∀ e ∈ G.edgeFinset,
      ∑ Q : Finset V, (if e.toFinset ⊆ Q then w Q else 0) = 1) :
    (cpLe 3 G : ℝ) ≤ (∑ Q, w Q) + 2 * (↑(∑ t ∈ range C.card, cap t) : ℝ) := by
  have hupper := split_cpLe_three_of_deficit_bounds G C hC hI cap hcap
  have hcore : uCount G C = C.card.choose 2 := card_innerEdges_of_isClique G C hC
  have hlower := split_fractional_price G C hI w hnonneg hsupport hcover
  rw [hcore] at hlower
  have hbound : (cpLe 3 G : ℝ) + C.card.choose 2 ≤
      (sCount G C : ℝ) + 2 * (↑(∑ t ∈ range C.card, cap t) : ℝ) := by exact_mod_cast hupper
  linarith

/-- Deficient bases concentrated at a small set of ports have a gap bounded by
twice the number of those ports times the largest deficit. -/
theorem split_fractional_gap_of_exceptional_ports (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V))
    (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y) (ports : Finset C) (D : ℕ)
    (hD : ∀ e : (⊤ : SimpleGraph C).edgeSet, C.card - (splitLists G C e).card ≤ D)
    (hports : ∀ e : (⊤ : SimpleGraph C).edgeSet, 0 < C.card - (splitLists G C e).card →
      ∃ v ∈ ports, v ∈ e.val)
    (w : Finset V → ℝ) (hnonneg : ∀ Q, 0 ≤ w Q)
    (hsupport : ∀ Q, w Q ≠ 0 → G.IsClique (Q : Set V))
    (hcover : ∀ e ∈ G.edgeFinset,
      ∑ Q : Finset V, (if e.toFinset ⊆ Q then w Q else 0) = 1) :
    (cpLe 3 G : ℝ) ≤ (∑ Q, w Q) + 2 * (↑(D * ports.card) : ℝ) := by
  classical
  let cap (t : ℕ) := if t < D then ports.card else 0
  have hcap (t : ℕ) (_ : t < C.card) (F : Finset (⊤ : SimpleGraph C).edgeSet)
      (hF : ∀ e ∈ F, t < C.card - (splitLists G C e).card)
      (hm : BasesMatching F) : F.card ≤ cap t := by
    by_cases ht : t < D
    · simp only [cap, ite_eq_left ht]
      exact matching_card_le_port_cover F ports hm
        (fun e he => hports e ((Nat.zero_le t).trans_lt (hF e he)))
    · have hF0 : F = ∅ := eq_empty_iff_forall_notMem.mpr
        (fun e he => ht ((hF e he).trans_le (hD e)))
      simp [hF0, cap, ht]
  have hfin : ((range C.card).filter fun t => t < D).card ≤ D := by
    calc
      _ ≤ (range D).card := card_le_card (fun t ht => mem_range.mpr (mem_filter.mp ht).2)
      _ = D := card_range D
  have hsum : (∑ t ∈ range C.card, cap t) ≤ D * ports.card := by
    calc
      _ = ∑ _t ∈ (range C.card).filter (fun t => t < D), ports.card := by
        rw [sum_filter]
      _ = ((range C.card).filter fun t => t < D).card * ports.card := by
        simp
      _ ≤ _ := Nat.mul_le_mul_right _ hfin
  have h := split_fractional_gap_of_deficit_bounds G C hC hI cap hcap w hnonneg hsupport hcover
  have hreal : (↑(∑ t ∈ range C.card, cap t) : ℝ) ≤ ↑(D * ports.card) := by
    exact_mod_cast hsum
  linarith

/-- Row omissions give a linear gap even when the exceptional set and its
additional allowance both grow as the square root of the core size. -/
theorem split_fractional_gap_of_sparse_exceptions (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V))
    (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (ports : Finset C) (r : ℕ) (hr : ports.card ≤ r) (hr₂ : r * r ≤ C.card)
    (hsize : 2 * C.card ≤ Cᶜ.card)
    (hmiss : ∀ a : C, (Cᶜ.filter (fun x => ¬ G.Adj x a.val)).card ≤
      C.card / 2 + if a ∈ ports then r else 0)
    (w : Finset V → ℝ) (hnonneg : ∀ Q, 0 ≤ w Q)
    (hsupport : ∀ Q, w Q ≠ 0 → G.IsClique (Q : Set V))
    (hcover : ∀ e ∈ G.edgeFinset,
      ∑ Q : Finset V, (if e.toFinset ⊆ Q then w Q else 0) = 1) :
    (cpLe 3 G : ℝ) ≤ (∑ Q, w Q) + 4 * (C.card : ℝ) := by
  classical
  have hsum (e : (⊤ : SimpleGraph C).edgeSet) :
      C.card - (splitLists G C e).card ≤
        ∑ a ∈ e.val.toFinset, (if a ∈ ports then r else 0) := by
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
        ∑ a ∈ B, (if a ∈ ports then r else 0) := by
      calc
        _ ≤ ∑ a ∈ B, (miss a).card := card_biUnion_le
        _ ≤ ∑ a ∈ B, (C.card / 2 + if a ∈ ports then r else 0) :=
          sum_le_sum fun a _ => hmiss a
        _ = _ := by rw [sum_add_distrib]; simp [hB]
    change C.card - (splitLists G C e).card ≤ ∑ a ∈ B, (if a ∈ ports then r else 0)
    omega
  have hD (e : (⊤ : SimpleGraph C).edgeSet) : C.card - (splitLists G C e).card ≤ 2 * r := by
    refine (hsum e).trans ((sum_le_sum (g := fun _ => r) fun a _ => by split <;> omega).trans ?_)
    simp [Sym2.card_toFinset_of_not_isDiag _
      ((⊤ : SimpleGraph C).not_isDiag_of_mem_edgeSet e.2)]
  have hex (e : (⊤ : SimpleGraph C).edgeSet) (he : 0 < C.card - (splitLists G C e).card) :
      ∃ v ∈ ports, v ∈ e.val := by
    by_contra! hh
    have hzero : (∑ a ∈ e.val.toFinset, (if a ∈ ports then r else 0)) = 0 :=
      sum_eq_zero fun a ha => ite_eq_right (fun hp => hh a hp (Sym2.mem_toFinset.mp ha))
    have := hsum e
    omega
  have hgap := split_fractional_gap_of_exceptional_ports G C hC hI ports (2 * r)
    hD hex w hnonneg hsupport hcover
  have hmul : (2 * r) * ports.card ≤ 2 * C.card := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 ((Nat.mul_le_mul_left r hr).trans hr₂)
  have hreal : (↑((2 * r) * ports.card) : ℝ) ≤ 2 * (C.card : ℝ) := by exact_mod_cast hmul
  linarith

/-- Missing crossings can pay the entire completion cost in the same graph. -/
theorem split_cpLe_three_le_M_of_paid_deficits (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V))
    (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (cap : ℕ → ℕ)
    (hcap : ∀ t < C.card, ∀ F : Finset (⊤ : SimpleGraph C).edgeSet,
      (∀ e ∈ F, t < C.card - (splitLists G C e).card) → BasesMatching F → F.card ≤ cap t)
    (hpaid : sCount G C + 2 * (∑ t ∈ range C.card, cap t) ≤ C.card * Cᶜ.card) :
    cpLe 3 G ≤ Mval (Fintype.card V) := by
  have hup := (split_cpLe_three_of_deficit_bounds G C hC hI cap hcap).trans hpaid
  have hsum : (C.card : ℤ) + (Cᶜ.card : ℤ) = (Fintype.card V : ℤ) := by
    exact_mod_cast (card_add_card_compl C)
  have hcost : (cpLe 3 G : ℤ) + (C.card.choose 2 : ℤ) ≤ (C.card : ℤ) * (Cᶜ.card : ℤ) := by
    exact_mod_cast hup
  have hquad := int_mul_pred_nonneg ((Cᶜ.card : ℤ) - 2 * C.card + 1)
  have hbin := two_mul_choose_two C.card
  have hle : (cpLe 3 G : ℤ) * 6 ≤ (Fintype.card V : ℤ) * ((Fintype.card V : ℤ) + 1) := by
    rw [← hsum]
    nlinarith only [hcost, hquad, hbin]
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 6)).mpr (by exact_mod_cast hle)

end QuadraticExteriorPalomar
