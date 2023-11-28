import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology

universe u v w

def UFCS_mk {α : Type u}(hα : ¬ (Countable α ) ) : TopologicalSpace α where
  IsOpen X := Set.Finite Xᶜ ∨ X = ∅
  isOpen_univ := by
    simp only [compl_univ, finite_empty, univ_eq_empty_iff, true_or]
  isOpen_inter := by
    simp only
    intro s t hs ht
    rw[Set.compl_inter]
    cases hs with
      | inl hsf =>
        cases ht with
          | inl htf =>
            left
            apply   Set.finite_union.mpr
            exact ⟨hsf,htf⟩
          | inr htn =>
            right
            rw[htn]
            simp only [inter_empty]
      | inr hsn =>
        right
        rw[hsn]
        simp only [empty_inter]
  isOpen_sUnion := by
    simp only
    intro s hs
    by_cases h : ⋃₀ s = ∅;
    · right
      exact h
    left
    push_neg at h
    set x := h.some with hxdef
    have hx : x ∈ ⋃₀ s := Set.Nonempty.some_mem h
    rw[Set.mem_sUnion] at hx
    cases hx with
      | intro t ht =>
        have htf : Set.Finite tᶜ := by
          have htn : t ≠ ∅ := by
            by_contra ht0
            rw[ht0] at ht
            simp at ht
          exact Or.resolve_right (hs t ht.1) htn
        apply Set.Finite.subset htf
        rw[Set.compl_subset_compl]
        intro x hx
        rw[Set.mem_sUnion]
        use t
        exact ⟨ht.1, hx⟩

section UncountableFiniteComplementTopology
variable (α : Type u)[t : TopologicalSpace α](hα : ¬ (Countable α )) (topology_eq : t = UFCS_mk hα)

theorem UFCS_open_iff{X : Set α} : IsOpen X ↔ Set.Finite Xᶜ ∨ X = ∅ := by
  rw[topology_eq]
  exact Iff.rfl

instance UFCS_T₁ : T1Space α := by
  rw [t1Space_iff_exists_open]
  intro x y hxy
  set U : Set α := {y}ᶜ with hU
  have hUopen : IsOpen U := by
    rw[UFCS_open_iff α hα topology_eq]
    left
    rw[hU]
    simp only [compl_compl, finite_singleton]
  have hx : x ∈ U := by
    rw[hU]
    simp only [mem_compl_iff, mem_singleton_iff]
    exact hxy
  have hy : y ∉ U := by
    simp only [mem_compl_iff, mem_singleton_iff, not_true, not_false_eq_true]
  exact ⟨U, hUopen, hx, hy⟩

instance UFCS_Infinite : Infinite α := by
  by_contra hinf
  simp only [not_infinite_iff_finite] at hinf
  have hαcount : Countable α := by
    exact False.elim (hα Finite.to_countable)
  exact hα hαcount


instance UFCS_nontrivial: Nontrivial α := by
  haveI := UFCS_Infinite α hα
  apply Infinite.instNontrivial α


theorem UFCS_not_T2 : ¬ T2Space α := by
    rw[t2Space_iff]
    push_neg
    haveI := UFCS_nontrivial α hα
    have hxye : ∃ x y : α, x ≠ y := by
      apply exists_pair_ne
    match hxye with
    | ⟨x,y, hxy⟩ =>
      use x
      use y
      constructor
      exact hxy
      intros U V hU hV hxU hyV
      push_neg
      rw[not_disjoint_iff_nonempty_inter]
      have hUV : Set.Finite Uᶜ ∧ Set.Finite Vᶜ := by
        constructor
        rw[UFCS_open_iff] at *
        apply Or.resolve_right hU
        by_contra hUc
        rw[hUc] at hxU
        simp only [mem_empty_iff_false] at hxU
        repeat assumption
        rw[UFCS_open_iff] at *
        apply Or.resolve_right hV
        by_contra hVc
        rw[hVc] at hyV
        simp only [mem_empty_iff_false] at hyV
        repeat assumption
      have hUcVc : Set.Finite (U ∩ V)ᶜ := by
        rw[Set.compl_inter]
        apply Set.finite_union.mpr
        exact hUV
      by_contra hUVc
      have huniv : (U ∩ V)ᶜ = univ := by
        simp[hUVc]
        rwa[← not_nonempty_iff_eq_empty]
      rw[huniv] at hUcVc
      have hUcVcuniv : Set.Countable univ := by
        apply Finite.countable (hUcVc)
      rw[countable_univ_iff] at hUcVcuniv
      exact hα  hUcVcuniv

end UncountableFiniteComplementTopology
