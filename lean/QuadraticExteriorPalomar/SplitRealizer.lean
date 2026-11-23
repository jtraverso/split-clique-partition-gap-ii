module

public import QuadraticExteriorPalomar.SplitLists
public import PaperV.HostRealizer

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset
open scoped BigOperators

/-- The retained color classes are realized in the genuine host system of
Paper V. Auxiliary colors never become host resources. -/
theorem partial_host_realizer_of_deficit_bounds {Core Host : Type*}
    [Fintype Core] [DecidableEq Core] [Fintype Host] [DecidableEq Host]
    (lists : (⊤ : SimpleGraph Core).edgeSet → Finset Host) (cap : ℕ → ℕ)
    (hcap : ∀ t < Fintype.card Core, ∀ F : Finset (⊤ : SimpleGraph Core).edgeSet,
      (∀ e ∈ F, t < Fintype.card Core - (lists e).card) →
      BasesMatching F → F.card ≤ cap t) :
    ∃ S : Finset (⊤ : SimpleGraph Core).edgeSet, ∃ host : S → Host,
      PaperV.Host.ProperOn (fun e : S => e.1.val.toFinset) (fun e => lists e.1) univ host ∧
      PaperV.UnitBoundary.ResFeasible
        (PaperV.Host.triRes (fun e : S => e.1.val.toFinset))
        (univ.image (fun e => (e, host e))) ∧
      Fintype.card (⊤ : SimpleGraph Core).edgeSet ≤ S.card + ∑ t ∈ range (Fintype.card Core), cap t := by
  classical
  obtain ⟨S, host, hmem, hinj, hcard⟩ :=
    partial_host_assignment_of_deficit_bounds lists cap hcap
  have hproper : PaperV.Host.ProperOn (fun e : S => e.1.val.toFinset)
      (fun e => lists e.1) univ host := by
    refine ⟨fun e _ => hmem e, ?_⟩
    intro e _ f _ hef hdisj heq
    obtain ⟨v, hv, hv'⟩ := not_disjoint_iff.mp hdisj
    exact hef (hinj e f v (Sym2.mem_toFinset.mp hv) (Sym2.mem_toFinset.mp hv') heq)
  exact ⟨S, host, hproper, PaperV.Host.resFeasible_of_properOn hproper, hcard⟩

/-- Realize only the requested bases. Lists can already exclude the radios
used by any fixed prefix. The budget charges matchings in that same residual. -/
theorem residual_host_realizer_of_deficit_bounds {Core Host : Type*}
    [Fintype Core] [DecidableEq Core] [Fintype Host] [DecidableEq Host]
    (R : Finset (⊤ : SimpleGraph Core).edgeSet)
    (lists : (⊤ : SimpleGraph Core).edgeSet → Finset Host) (cap : ℕ → ℕ)
    (hcap : ∀ t < Fintype.card Core, ∀ F : Finset (⊤ : SimpleGraph Core).edgeSet,
      F ⊆ R → (∀ e ∈ F, t < Fintype.card Core - (lists e).card) →
      BasesMatching F → F.card ≤ cap t) :
    ∃ S : Finset (⊤ : SimpleGraph Core).edgeSet, S ⊆ R ∧ ∃ host : S → Host,
      PaperV.Host.ProperOn (fun e : S => e.1.val.toFinset) (fun e => lists e.1) univ host ∧
      PaperV.UnitBoundary.ResFeasible
        (PaperV.Host.triRes (fun e : S => e.1.val.toFinset))
        (univ.image (fun e => (e, host e))) ∧
      R.card ≤ S.card + ∑ t ∈ range (Fintype.card Core), cap t := by
  classical
  let E := (⊤ : SimpleGraph Core).edgeSet
  let c := Fintype.card Core
  let full (e : E) : Finset (Host ⊕ ℕ) :=
    if e ∈ R then (lists e).image Sum.inl else (range c).image Sum.inr
  have hfull (e : E) (he : e ∈ R) : full e = (lists e).image Sum.inl := ite_eq_left he
  have hcap' (t : ℕ) (ht : t < c) (F : Finset E)
      (hF : ∀ e ∈ F, t < c - (full e).card) (hm : BasesMatching F) : F.card ≤ cap t := by
    have hsub : F ⊆ R := by
      intro e he
      by_contra hn
      have hc : (full e).card = c := by
        rw [show full e = (range c).image Sum.inr from ite_eq_right hn,
          card_image_of_injective _ Sum.inr_injective, card_range]
      have hlt := hF e he
      omega
    exact hcap t ht F hsub (fun e he => by
      simpa only [hfull e (hsub he), card_image_of_injective _ Sum.inl_injective] using hF e he) hm
  obtain ⟨A, f, hmem, hproper, hcard⟩ := partial_host_assignment_of_deficit_bounds full cap hcap'
  let S := A ∩ R
  let toA (e : S) : A := ⟨e.val, (mem_inter.mp e.2).1⟩
  have hreal (e : S) : ∃ x ∈ lists e.val, f (toA e) = Sum.inl x := by
    have he := hmem (toA e)
    change f (toA e) ∈ full e.val at he
    rw [hfull e.val (mem_inter.mp e.2).2] at he
    obtain ⟨x, hx, hfx⟩ := mem_image.mp he
    exact ⟨x, hx, hfx.symm⟩
  choose host hhost hcol using hreal
  have hproper' : PaperV.Host.ProperOn (fun e : S => e.1.val.toFinset)
      (fun e => lists e.1) univ host := by
    refine ⟨fun e _ => hhost e, ?_⟩
    intro e _ f' _ hef hdisj hh
    obtain ⟨v, hv, hv'⟩ := not_disjoint_iff.mp hdisj
    have heq := hproper (toA e) (toA f') v
      (Sym2.mem_toFinset.mp hv) (Sym2.mem_toFinset.mp hv')
      ((hcol e).trans (by rw [hh, ← hcol f']))
    have heq' : e.val = f'.val := congrArg (fun a : A => a.val) heq
    exact hef (Subtype.ext heq')
  refine ⟨S, fun _ he => (mem_inter.mp he).2, host, hproper',
    PaperV.Host.resFeasible_of_properOn hproper', ?_⟩
  have hunion : (A ∪ R).card ≤ Fintype.card E := card_le_univ _
  have hcounts := card_union_add_card_inter A R
  change Fintype.card E ≤ A.card + ∑ t ∈ range c, cap t at hcard
  change R.card ≤ (A ∩ R).card + ∑ t ∈ range c, cap t
  omega

end QuadraticExteriorPalomar
