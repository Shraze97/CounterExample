import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology

universe u v w

/--Making the Fortissimo Space-/
def FortissiomoSpace_mk{α : Type u}(p : α) : TopologicalSpace α where
  IsOpen X := p ∈ Xᶜ  ∨ Set.Countable Xᶜ
  isOpen_univ := by
    simp only [compl_univ, mem_empty_iff_false, countable_empty, or_true]
  isOpen_inter := by
    simp only [mem_inter_iff]
    intro s t hs ht
    cases hs with
    | inl hps  =>
      left
      rw[Set.compl_inter]
      simp only [mem_union]
      left
      assumption
    | inr hcs =>
      cases ht with
      | inl hpt =>
        left
        rw[Set.compl_inter]
        simp only [mem_union]
        right
        assumption
      | inr hct =>
        right
        rw[Set.compl_inter]
        apply Set.Countable.union hcs hct
  isOpen_sUnion := by
    simp only [mem_sUnion]
    intro s hs
    by_cases hp : p ∈ (⋃₀ s)ᶜ
    · left
      assumption
    · right
      simp only [mem_compl_iff, mem_sUnion, not_exists, not_and, not_forall, not_not, exists_prop] at hp
      cases hp with
      | intro t ht =>
        have hsc : Set.Countable tᶜ :=by
          have hpt : ¬ (p ∈ tᶜ) := by
            intro hpt
            apply hpt ht.2
          apply Or.resolve_left (hs t ht.1) hpt
        have hst :  (⋃₀ s)ᶜ ⊆ tᶜ  := by
          rw[Set.compl_subset_compl]
          intro x hx
          rw[Set.mem_sUnion]
          use t
          exact ⟨ht.1, hx⟩
        exact Set.Countable.mono hst hsc

section FortissiomoSpace

variable{α : Type u}(p : α)(hcount : ¬ Countable α)[t : TopologicalSpace α](topology_eq : t = FortissiomoSpace_mk p)

/--Fortissimo Space is open if either p is contained in the complement of X or complement of X is countable-/
theorem FS_open_iff : IsOpen X = (p ∈ Xᶜ  ∨ Set.Countable Xᶜ) := by
  rw[topology_eq]
  rfl

/--Fortissimo Space is a T5 Space-/
instance FS_T₅ : T5Space α := by

  sorry

end FortissiomoSpace
