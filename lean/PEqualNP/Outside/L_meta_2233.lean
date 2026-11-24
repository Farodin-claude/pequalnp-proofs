import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

theorem ors_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

/-- Membership in the OR closures, gate by gate (the pattern of the cone lemmas of L_meta_1490). -/
theorem ors_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [ors_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] = (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, hij⟩
        refine ⟨by simp; omega, ?_⟩
        rcases hij with hij | ⟨ho, w, hw, h1, h2, h3⟩
        · exact Or.inl hij
        · exact Or.inr ⟨ho, w, hw, h1, h2, by rw [key (w - n) (by omega)]; exact h3⟩
      · rintro ⟨_, hij⟩
        refine ⟨h, ?_⟩
        rcases hij with hij | ⟨ho, w, hw, h1, h2, h3⟩
        · exact Or.inl hij
        · exact Or.inr ⟨ho, w, hw, h1, h2, by rw [key (w - n) (by omega)] at h3; exact h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
          gs.length :: (if g.op = GateOp.or then
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) else []) := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_cons]
      constructor
      · rintro (hij | hij)
        · exact ⟨by simp, Or.inl hij⟩
        · refine ⟨by simp, Or.inr ?_⟩
          split_ifs at hij with ho
          · obtain ⟨w, hw, hi⟩ := List.mem_flatMap.mp hij
            rw [List.mem_filter, decide_eq_true_eq] at hw
            exact ⟨ho, w, hw.1, hw.2.1, hw.2.2, by rw [key (w - n) (by omega)]; exact hi⟩
          · simp at hij
      · rintro ⟨_, hij | ⟨ho, w, hw, h1, h2, h3⟩⟩
        · exact Or.inl hij
        · right
          rw [if_pos ho]
          refine List.mem_flatMap.mpr ⟨w, List.mem_filter.mpr ⟨hw, by simp [h1, h2]⟩, ?_⟩
          rw [key (w - n) (by omega)] at h3
          exact h3
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem reach_iff (n : ℕ) (C : Circuit) (w i : ℕ) :
    OrReaches n C w i ↔ n ≤ w ∧ w - n < C.gates.length ∧ (i = w - n ∨ ((gateAt C (w - n)).op = GateOp.or ∧
      ∃ v ∈ (gateAt C (w - n)).inputs, n ≤ v ∧ v < w ∧ OrReaches n C v i)) := by
  unfold OrReaches orSets
  rw [ors_char]
  unfold gateAt
  constructor
  · rintro ⟨hw, hj, hij⟩
    refine ⟨hw, hj, ?_⟩
    rcases hij with hij | ⟨ho, v, hv, h1, h2, h3⟩
    · exact Or.inl hij
    · exact Or.inr ⟨ho, v, hv, h1, by omega, h1, h3⟩
  · rintro ⟨hw, hj, hij⟩
    refine ⟨hw, hj, ?_⟩
    rcases hij with hij | ⟨ho, v, hv, h1, h2, -, h3⟩
    · exact Or.inl hij
    · exact Or.inr ⟨ho, v, hv, h1, by omega, h3⟩

/-- The last OR step of a nontrivial OR path down to gate `x`. -/
theorem last_step (n : ℕ) (C : Circuit) (x : ℕ) :
    ∀ w, OrReaches n C w x → w ≠ n + x →
      ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧
        n + x ∈ (gateAt C h).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr hne
    obtain ⟨hw, hk, hcase⟩ := (reach_iff n C w x).mp hr
    rcases hcase with hx | ⟨ho, v, hv, h1, h2, h3⟩
    · omega
    · have hself : OrReaches n C w (w - n) := (reach_iff n C w (w - n)).mpr ⟨hw, hk, Or.inl rfl⟩
      by_cases hvx : v = n + x
      · exact ⟨w - n, hk, ho, hself, hvx ▸ hv⟩
      · obtain ⟨h, hh, hho, hvh, hin⟩ := ih v h2 h3 hvx
        exact ⟨h, hh, hho, (reach_iff n C w h).mpr ⟨hw, hk, Or.inr ⟨ho, v, hv, h1, h2, hvh⟩⟩, hin⟩

theorem main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  classical
  set o := C.output
  set D := (Finset.range C.gates.length).filter
    (fun i => (gateAt C i).op = GateOp.or ∧ OrReaches n C o i) with hDdef
  have hDset : Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C o i} = D.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [D]
  rw [hDset]
  have hdisj : Disjoint F D := by
    rw [Finset.disjoint_left]
    intro x hxF hxD
    have h1 := (hF x hxF).2.1
    have h2 := (Finset.mem_filter.mp hxD).2.1
    rw [h1] at h2
    cases h2
  set X := F ∪ D
  have hXr : ∀ x ∈ X, OrReaches n C o x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (hF x hx).2.2
    · exact (Finset.mem_filter.mp hx).2.2
  set Y := X.filter (fun x => o ≠ n + x)
  have H : ∀ x, ∃ p : ℕ × Fin 2, x ∈ Y →
      p.1 ∈ D ∧ (gateAt C p.1).inputs.getD p.2 0 = n + x := by
    intro x
    by_cases hx : x ∈ Y
    · obtain ⟨hxX, hne⟩ := Finset.mem_filter.mp hx
      obtain ⟨h, hh, hho, hoh, hin⟩ := last_step n C x o (hXr x hxX) hne
      have hlen : (gateAt C h).inputs.length = 2 := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hh]
        exact hC.2.2 _ (List.getElem_mem hh)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
      rw [hab] at hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      have hD : h ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hho, hoh⟩
      rcases hin with hin | hin
      · exact ⟨(h, 0), fun _ => ⟨hD, by rw [hab]; simp [hin]⟩⟩
      · exact ⟨(h, 1), fun _ => ⟨hD, by rw [hab]; simp [hin]⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hx⟩
  choose f hf using H
  have hY : Y.card ≤ (D ×ˢ (Finset.univ : Finset (Fin 2))).card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      exact Finset.mem_product.mpr ⟨(hf x hx).1, Finset.mem_univ _⟩
    · intro x hx y hy hxy
      have h1 := (hf x hx).2
      have h2 := (hf y hy).2
      rw [hxy] at h1
      omega
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hY
  have hXY : X.card ≤ Y.card + 1 := by
    have h2 : (X.filter (fun x => o = n + x)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have := (Finset.mem_filter.mp ha).2
      have := (Finset.mem_filter.mp hb).2
      omega
    have hsub : X ⊆ Y ∪ X.filter (fun x => o = n + x) := by
      intro x hx
      by_cases h : o = n + x
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hXc : X.card = F.card + D.card := Finset.card_union_of_disjoint hdisj
  omega

end PEqualNP.Outside.L_meta_2233_aux

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  exact PEqualNP.Outside.L_meta_2233_aux.main
