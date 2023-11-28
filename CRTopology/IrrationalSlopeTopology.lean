import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology TopologicalSpace

universe u v w

@[ext]
structure UpperHalfRationals where
  x : ℚ
  y : ℚ
  hy : 0 ≤  y


notation "ℚ+" => UpperHalfRationals


def B (ε : ℝ)(ζ : ℝ) : Set ℚ+ := {z : ℚ+ | ‖z.x - ζ‖ < ε ∧ z.y = 0}

def nhs_dit (θ : ℝ)(ε : ℝ)(z : ℚ+) : Set ℚ+ := {z} ∪ B ε (z.x - z.y / θ) ∪ B ε (z.x + z.y / θ)

lemma B_le (ε₁ : ℝ)(ε₂ : ℝ )(z : ℝ)(hε : ε₁ ≥  ε₂) : B ε₂ z ⊆ B ε₁ z :=
  by
    rw[B,B]
    simp only [Real.norm_eq_abs, setOf_subset_setOf, and_imp]
    intro x hx h
    apply And.intro
    · apply lt_of_lt_of_le hx
      assumption
    · assumption


lemma nhs_le (θ : ℝ)(ε₁ : ℝ)(ε₂ : ℝ )(z : ℚ+)(hε : ε₁ ≥  ε₂) : nhs_dit θ ε₂ z ⊆ nhs_dit θ ε₁ z := by
  rw[nhs_dit,nhs_dit]
  intro x hx
  simp only [singleton_union, mem_union, mem_insert_iff]
  simp only [singleton_union, mem_union, mem_insert_iff] at hx
  cases hx with
    | inl hl =>
      cases hl with
        | inl hll =>
          left
          left
          assumption
        | inr hlr =>
          left
          right
          apply B_le<;>
          assumption
    | inr hr  =>
      right
      apply B_le<;>
      assumption


def filter_gen (θ : ℝ)(z : ℚ+) : Filter ℚ+
    where
  sets := { t | ∃ ε : ℝ , t ⊇  nhs_dit θ ε z ∧ ε > 0}
  univ_sets := by
    simp only [gt_iff_lt, mem_setOf_eq, subset_univ, true_and]
    use 1
    simp only [zero_lt_one]
  sets_of_superset := by
    rintro x y hx hxy
    simp only [mem_setOf_eq] at hx
    simp only [mem_setOf_eq]
    match hx with
      | ⟨ε,hx,hε⟩ =>
        use ε
        constructor
        trans
        exact hxy
        exact hx
        assumption
  inter_sets := by
    rintro x y ⟨ε₁,hx⟩ ⟨ε₂,hy⟩
    use min ε₁ ε₂
    constructor
    apply subset_inter
    · trans
      apply nhs_le θ ε₁ (min ε₁ ε₂)
      simp only [ge_iff_le, min_le_iff, le_refl, true_or]
      exact hx.1
    · trans
      apply nhs_le θ ε₂ (min ε₁ ε₂)
      simp only [ge_iff_le, min_le_iff, le_refl, or_true]
      exact hy.1
    apply lt_min hx.2 hy.2


def IrrationalSlopeTopology_mk (θ : ℝ)(hθ : Irrational θ) : TopologicalSpace ℚ+ :=
  TopologicalSpace.mkOfNhds (filter_gen θ)

lemma xaxisnhs (θ : ℝ)(ε : ℝ)(z : ℚ+)(hy : z.y = 0)(hε : ε > 0) : nhs_dit θ ε z = B ε z.x := by
  rw[nhs_dit]
  simp only [hy, Rat.cast_zero, zero_div, sub_zero, add_zero]
  have hz : z ∈ B ε z.x := by
    rw[B]
    simp
    constructor<;>
    assumption
  simp only [singleton_union, hz, insert_eq_of_mem, union_self]

lemma purenhsdit (θ : ℝ): pure ≤ filter_gen θ := by
  intros z n hnz
  simp only [mem_pure]
  rw[filter_gen] at hnz
  simp at hnz
  match hnz with
    | ⟨ε,hnε,_⟩ =>
      apply Set.mem_of_subset_of_mem hnε
      rw[nhs_dit]
      simp only [singleton_union, mem_union, mem_insert_iff, true_or]

lemma nhs_dit_subs (θ : ℝ)(ε : ℝ)(p : ℝ)(a : ℚ+)(hay : a.y = 0)(hinq : |a.x - p| < ε )(hε : ε > 0 ) : ∃ ε₂ : ℝ , nhs_dit θ ε₂ a ⊆ B ε p ∧ ε₂ > 0  := by
  by_cases hap : a.x - p = 0
  · use ε
    rw[xaxisnhs θ ε a hay]
    have hpa : p = a.x := by
      linarith
    rw[←hpa]
    constructor
    triv
    repeat assumption
  · set r : ℝ := |a.x - p| with hr
    set ε₂ := (ε - r)/2  with hε₂
    use ε₂
    constructor
    rw[xaxisnhs θ ε₂ a hay]
    rw[B,B]
    simp only [Real.norm_eq_abs, setOf_subset_setOf, and_imp]
    intro z hz h
    rw[← hr] at hz
    constructor
    have hzp : |z.x - p| ≤ |z.x - a.x| + |a.x - p| := by
      norm_num
      have hzpeq : z.x - p = (z.x - a.x) + (a.x - p) := by
        linarith
      rw[hzpeq]
      apply abs_add
    have hεr : ε > (ε + r)/2 := by
      linarith
    have hεrmod : |↑z.x - a.x| + |a.x - p| < (ε - r)/2 + r := by
      norm_num
      rw[← hr]
      exact hz
    linarith
    assumption
    repeat linarith

theorem nhds_dit_filter_gen (θ : ℝ)(hθ : Irrational θ)(z : ℚ+) : @nhds ℚ+ (IrrationalSlopeTopology_mk θ hθ) z = filter_gen θ z:= by
  apply nhds_mkOfNhds
  exact purenhsdit θ
  intros a s hs
  rw[filter_gen] at hs
  simp at hs
  match hs with
    | ⟨ε,hsε,hε⟩ =>
      set t := nhs_dit θ ε a with ht
      use t
      constructor
      rw[filter_gen]
      simp only [gt_iff_lt, Filter.mem_mk, mem_setOf_eq]
      use ε
      constructor
      assumption
      intros a' hat
      rw[filter_gen]
      simp only [gt_iff_lt, Filter.mem_mk, mem_setOf_eq]
      rw[ht,nhs_dit] at hat
      simp at hat
      cases hat with
      | inl hl =>
        cases hl with
        | inl hll =>
          rw[hll]
          use ε
        | inr hlr =>
          rw[B] at hlr
          simp only [Real.norm_eq_abs, mem_setOf_eq] at hlr
          have lem : ∃ ε₂ : ℝ , nhs_dit θ ε₂ a' ⊆ B ε (↑a.x - ↑a.y / θ) ∧ ε₂ > 0 := nhs_dit_subs θ ε (a.x - a.y / θ) a' hlr.2 hlr.1 hε
          match lem with
          | ⟨ε₂,hε₂⟩ =>
            use ε₂
            constructor
            trans
            exact hsε
            rw[ht,nhs_dit]
            trans
            any_goals exact hε₂.1
            intro x hx
            simp only [singleton_union, mem_union, mem_insert_iff]
            left
            right
            assumption
            exact hε₂.2
      | inr hr =>
        rw[B] at hr
        simp only [Real.norm_eq_abs, mem_setOf_eq] at hr
        have lem : ∃ ε₂ : ℝ , nhs_dit θ ε₂ a' ⊆ B ε (↑a.x + ↑a.y / θ) ∧ ε₂ > 0 := nhs_dit_subs θ ε (a.x + a.y / θ) a' hr.2 hr.1 hε
        match lem with
          | ⟨ε₂,hε₂⟩ =>
            use ε₂
            constructor
            trans
            exact hsε
            rw[ht,nhs_dit]
            trans
            any_goals exact hε₂.1
            simp only [singleton_union, subset_union_right]
            exact hε₂.2

section IrrationalSlopeTopology


variable (θ : ℝ)(hθ : Irrational θ)[t : TopologicalSpace ℚ+](topology_eq : t = IrrationalSlopeTopology_mk θ hθ)

theorem IST_nhs_iff (z : ℚ+)(s : Set ℚ+) : s ∈ @nhds ℚ+ t z ↔ ∃ ε : ℝ , s ⊇ nhs_dit θ ε z ∧ ε > 0 := by
  rw[topology_eq]
  rw[ nhds_dit_filter_gen θ hθ z]
  rw[filter_gen]
  simp only [gt_iff_lt, Filter.mem_mk, mem_setOf_eq]

lemma B_dijoint_ball_construct (z₁ : ℝ)(z₂ : ℝ)(hz1z2 : z₁ ≠ z₂) : ∃ ε₁ ε₂ : ℝ , (B (ε₁) z₁ ∩ B (ε₂) z₂ = ∅) ∧ (ε₁ > 0) ∧ (ε₂ > 0) := by
  set ε₁ := |z₁ - z₂|/3 with hε₁
  use ε₁, ε₁
  have hz : |z₁ - z₂| > 0 := by
    simp[hz1z2]
    by_contra lem
    apply hz1z2
    linarith
  constructor
  rw[B,B]
  simp only [Real.norm_eq_abs]
  by_contra h
  push_neg at h
  rw[ nonempty_def] at h
  match h with
  |⟨x,hx⟩  =>
    simp at hx
    match hx with
    | ⟨⟨hax,_⟩,⟨hbx,_⟩⟩ =>
    have hxz : |z₁ - z₂| ≤ |z₁ - x.x| + |x.x - z₂| := by
      norm_num
      have hzpeq : z₁ - z₂ = (z₁ - x.x) + (x.x - z₂) := by
        linarith
      rw[hzpeq]
      apply abs_add
    have hmodxz : |x.x - z₁| = |z₁ - x.x| := by
      apply abs_sub_comm
    have hε₁ε₂ : |z₁ - x.x| + |x.x - z₂| < ε₁ + ε₁ := by
      rw[←hmodxz,hε₁]
      linarith
    have hab : |z₁ - z₂| < ε₁ + ε₁ := by
      linarith
    rw[hε₁] at hab
    linarith
  constructor<;>
  linarith

lemma distinct_points_z1_z2 (z1 : ℚ+)(z2 : ℚ+)(hlemma : z1 ≠ z2):  z1.x - z1.y/θ ≠ z2.x - z2.y/θ := by
  by_contra h
  have hz : z1.x - z2.x = (z1.y - z2.y)/θ :=
    calc
      z1.x - z2.x = z1.x - z1.y/θ + z1.y/θ - z2.x := by
        simp only [sub_add_cancel]
      _ = z2.x - z2.y/θ + z1.y/θ - z2.x := by
        rw[h]
      _ = (z1.y - z2.y)/θ := by
        ring
  by_cases hzy_eq : z1.y = z2.y
  · have hzx : z1.x = z2.x := by
      rw[hzy_eq] at hz
      simp only [sub_self, zero_div] at hz
      norm_cast at hz
      linarith
    have hzeq : z1 = z2 := by
      apply UpperHalfRationals.ext
      simp only [hzx,hzy_eq]
      exact hzy_eq
    exact hlemma hzeq
  · apply Irrational.ne_rat
    apply Irrational.rat_div
    exact hθ
    have hzy : z1.y - z2.y ≠ 0 := by
      intro hzya
      apply hzy_eq
      linarith
    exact hzy
    norm_cast at hz
    exact hz.symm

lemma distinct_points_z1_z2_diff (z1 : ℚ+)(z2 : ℚ+)(hlemma : z1 ≠ z2):  z1.x - z1.y/θ ≠ z2.x + z2.y/θ := by
  by_contra h
  have hz : z1.x - z2.x = (z1.y + z2.y)/θ :=
    calc
      z1.x - z2.x = z1.x - z1.y/θ + z1.y/θ - z2.x := by
        simp only [sub_add_cancel]
      _ = z2.x + z2.y/θ + z1.y/θ - z2.x := by
        rw[h]
      _ = (z1.y + z2.y)/θ := by
        ring
  norm_cast at hz
  have hy1 : z1.y ≥  0 := z1.hy
  have hy2 :z2.y ≥ 0 := z2.hy
  by_cases hzy_eq : z1.y = -z2.y
  · have hy10 : z1.y = 0 := by
      linarith
    have hy20 : z2.y = 0 := by
      linarith
    have hzeq : z1 = z2 := by
      rw[hy10,hy20] at hz
      simp at hz
      norm_cast at hz
      apply UpperHalfRationals.ext
      repeat linarith
    exact hlemma hzeq
  · apply Irrational.ne_rat
    apply Irrational.rat_div
    exact hθ
    have hzy : z1.y + z2.y ≠ 0 := by
      intro hzya
      apply hzy_eq
      linarith
    exact hzy
    exact hz.symm

lemma distinct_sets{A : Set ℚ+}{B : Set ℚ+}{C : Set ℚ+}{D : Set ℚ+}(hA : A ∩ D = ∅)(hB : B ∩ D = ∅)(hC : C ∩ D = ∅):  (A ∪ B ∪ C) ∩ D = ∅ := by
  repeat rw[Set.union_inter_distrib_right]
  rw[hA,hB,hC]
  simp only [union_self]

lemma distict_sets_2{A : Set ℚ+}{B : Set ℚ+}{C : Set ℚ+}{D : Set ℚ+}{E : Set ℚ+}{F : Set ℚ+}(hAD : A ∩ D = ∅)(hBD : B ∩ D = ∅)(hCD : C ∩ D = ∅)(hAE : A ∩ E = ∅)(hBE : B ∩ E = ∅)(hCE : C ∩ E = ∅)(hAF : A ∩ F = ∅)(hBF : B ∩ F = ∅)(hCF : C ∩ F = ∅):  (A ∪ B ∪ C) ∩ (D ∪ E ∪ F) = ∅ := by
  repeat rw[Set.inter_distrib_left]
  rw[distinct_sets hAD hBD hCD]
  rw[distinct_sets hAE hBE hCE]
  rw[distinct_sets hAF hBF hCF]
  simp only [union_self]



instance IST_T₂ : T2Space ℚ+ := by
  rw[t2Space_iff_disjoint_nhds]
  intro z1 z2 hz1z2
  rw[Filter.disjoint_iff]

  sorry


end IrrationalSlopeTopology
