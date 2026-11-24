import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2606_aux

open PEqualNP.CircuitLowerBounds

/-- One evaluation step: append the value of gate `g` to the wire list `w`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool),
    ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨t, ht, hl⟩ := fold_prefix gs (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, -⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

theorem fold_gate : ∀ (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
    (∀ i ∈ (gs[j]).inputs, i < x.length + j) →
    (gs.foldl step x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (gs.foldl step x).getD i false)
  | [], _, _, hj, _ => absurd hj (by simp)
  | g :: gs, x, 0, _, hrb => by
    simp only [List.getElem_cons_zero, Nat.add_zero] at hrb ⊢
    rw [List.foldl_cons, fold_getD_lt _ _ _ (by simp [step])]
    have hm : g.inputs.map (fun i => (gs.foldl step (step x g)).getD i false)
        = g.inputs.map (fun i => x.getD i false) := by
      refine List.map_congr_left fun i hi => ?_
      have hix := hrb i hi
      rw [fold_getD_lt _ _ _ (by simp [step]; omega)]
      simp only [step]
      rw [List.getD_append _ _ _ _ hix]
    rw [hm]
    simp [step]
  | g :: gs, x, j + 1, hj, hrb => by
    simp only [List.getElem_cons_succ] at hrb ⊢
    have hlen : (step x g).length = x.length + 1 := by simp [step]
    have := fold_gate gs (step x g) j (by simpa using hj) (fun i hi => by
      have := hrb i hi; omega)
    rw [hlen] at this
    rw [List.foldl_cons, show x.length + (j + 1) = x.length + 1 + j by omega]
    exact this

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hj]

/-- Pointwise order on wire lists. -/
def Le (w1 w2 : List Bool) : Prop := ∀ i, w1.getD i false = true → w2.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w1 w2 : List Bool)
    (h : Le w1 w2) (hv : g.op.eval (g.inputs.map fun i => w1.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at hv ⊢ <;>
    simp only [GateOp.eval, List.all_eq_true, List.any_eq_true, List.mem_map, id] at hv ⊢
  · rintro _ ⟨a, ha, rfl⟩
    exact h a (hv _ ⟨a, ha, rfl⟩)
  · obtain ⟨_, ⟨a, ha, rfl⟩, hb⟩ := hv
    exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩

theorem step_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w1 w2 : List Bool)
    (hl : w1.length = w2.length) (h : Le w1 w2) :
    (step w1 g).length = (step w2 g).length ∧ Le (step w1 g) (step w2 g) := by
  refine ⟨by simp [step, hl], fun i hi => ?_⟩
  simp only [step] at hi ⊢
  rcases lt_trichotomy i w1.length with hlt | rfl | hgt
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ le_rfl] at hi
    rw [hl, List.getD_append_right _ _ _ _ le_rfl] at *
    simp only [Nat.sub_self, List.getD_cons_zero] at hi ⊢
    exact eval_mono g hg w1 w2 h hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

theorem fold_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (w1 w2 : List Bool), w1.length = w2.length → Le w1 w2 →
      Le (gs.foldl step w1) (gs.foldl step w2)
  | [], _, _, _, _, h => h
  | g :: gs, hg, w1, w2, hl, h => by
    obtain ⟨hl', h'⟩ := step_mono g (hg g (List.mem_cons_self ..)) w1 w2 hl h
    exact fold_mono gs (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _ _ hl' h'

theorem ofFn_le (n : ℕ) (x y : Fin n → Bool) (hxy : x ≤ y) : Le (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn] at hi ⊢
    exact (Bool.le_iff_imp.mp (hxy ⟨i, hin⟩)) hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

theorem main : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 x2 x1 → (∀ (x4 : ℕ), Monotone fun (x5 : Fin x2 → Bool) => PEqualNP.BlindGate.wireValue x1 x2 x5 x4) ∧ ∀ (x4 x5 x6 : ℕ), x1.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → ∀ (x8 : Fin x2 → Bool), PEqualNP.BlindGate.wireValue x1 x2 x8 (x2 + x4) = (PEqualNP.BlindGate.wireValue x1 x2 x8 x5 && PEqualNP.BlindGate.wireValue x1 x2 x8 x6) := by
  intro C n hC
  obtain ⟨hao, hrb, -⟩ := hC
  refine ⟨fun w x y hxy => ?_, fun j a b hj x => ?_⟩
  · have := fold_mono C.gates hao _ _ (by simp) (ofFn_le n x y hxy) w
    exact Bool.le_iff_imp.mpr this
  · obtain ⟨hjl, hjg⟩ := List.getElem?_eq_some_iff.mp hj
    have hrd := hrb j hjl
    rw [gateAt_eq C j hjl, hjg] at hrd
    unfold PEqualNP.BlindGate.wireValue
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    have := fold_gate C.gates (List.ofFn x) j hjl (by
      rw [hlen, hjg]; exact hrd)
    rw [hlen, hjg] at this
    show (C.gates.foldl step (List.ofFn x)).getD (n + j) false = _
    rw [this]
    simp [GateOp.eval]
    rfl

end PEqualNP.Outside.L_meta_2606_aux

theorem PEqualNP.Outside.L_meta_2606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 x2 x1 → (∀ (x4 : ℕ), Monotone fun (x5 : Fin x2 → Bool) => PEqualNP.BlindGate.wireValue x1 x2 x5 x4) ∧ ∀ (x4 x5 x6 : ℕ), x1.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → ∀ (x8 : Fin x2 → Bool), PEqualNP.BlindGate.wireValue x1 x2 x8 (x2 + x4) = (PEqualNP.BlindGate.wireValue x1 x2 x8 x5 && PEqualNP.BlindGate.wireValue x1 x2 x8 x6) := by
  exact PEqualNP.Outside.L_meta_2606_aux.main
