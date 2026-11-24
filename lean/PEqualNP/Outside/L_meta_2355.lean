import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2355_aux

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

/-- The value of wire `i` of `C` on input `x`. -/
def V (C : Circuit) (x : List Bool) (i : ℕ) : Bool := (C.wires x).getD i false

theorem V_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    V C x i = x.getD i false := by
  unfold V
  rw [wires_eq, fold_getD_lt _ _ _ hi]

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hj]

theorem V_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    V C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map (V C x)) := by
  unfold V
  rw [wires_eq, ← hx]
  apply fold_gate C.gates x j hj
  intro i hi
  have := hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
  omega

theorem V_or (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or) (a : ℕ)
    (ha : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) (hv : V C x a = true) :
    V C x (n + j) = true := by
  rw [gateAt_eq C j hj] at hop ha
  rw [V_gate n C x hx hrb j hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨a, ha, hv⟩

theorem V_and (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and)
    (h0 : V C x ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = true)
    (h1 : V C x ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = true) :
    V C x (n + j) = true := by
  rw [gateAt_eq C j hj] at hop h0 h1
  rw [V_gate n C x hx hrb j hj, hop]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ (List.getElem_mem hj))
  rw [hab] at h0 h1 ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  simp [GateOp.eval, h0, h1]

/-- The OR-reach relation of the statement. -/
def Reach (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = GateOp.or ∧
    ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs)

theorem V_reach (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) {a b : ℕ} (h : Reach n C a b)
    (hv : V C x a = true) : V C x b = true := by
  induction h with
  | refl => exact hv
  | tail _ hst ih =>
    obtain ⟨-, rj, rfl, hrj, hop, hin⟩ := hst
    exact V_or n C x hx hrb rj hrj hop _ hin ih

end PEqualNP.Outside.L_meta_2355_aux

open PEqualNP.Outside.L_meta_2355_aux in
theorem PEqualNP.Outside.L_meta_2355 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (p : Fin N) (l : Fin M) (L : List (ℕ × ℕ)), I p l → ((∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) ∧ (L.filter (fun e1 => decide (e1.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = lw l))).length ∈ ({1, 2} : Finset ℕ)) → ∃ gv ∈ L, gv.2 = pw p ∧ ∀ q : Fin N, R (pw q) gv.1 → I q l := by
  intro n N M pw lw I C hC _ _ _ hpn hln hsound R hR T hT p l L _ hL
  subst hR hT
  classical
  obtain ⟨⟨j0, L1, L2, hj0, hop0, hr0, hT1, hT2, rfl⟩, hside, hxc, -⟩ := hL
  obtain ⟨_, hrb, h2⟩ := hC
  by_contra hcon
  push_neg at hcon
  -- one shadow point off `l` for every x-leaf
  let f : ℕ × ℕ → Fin N := fun gv =>
    if h : ∃ q : Fin N, Reach n C (pw q) gv.1 ∧ ¬ I q l then h.choose else p
  let XL := (L1 ++ L2).filter (fun e1 => decide (e1.2 = pw p))
  let P : Finset (Fin N) := (XL.map f).toFinset
  have hf : ∀ gv ∈ L1 ++ L2, gv.2 = pw p → Reach n C (pw (f gv)) gv.1 ∧ ¬ I (f gv) l := by
    intro gv hgv hpv
    have h : ∃ q : Fin N, Reach n C (pw q) gv.1 ∧ ¬ I q l := hcon gv hgv hpv
    simp only [f, dif_pos h]
    exact h.choose_spec
  have hPcard : P.card ≤ 2 := by
    have h1 := List.toFinset_card_le (XL.map f)
    rw [List.length_map] at h1
    have hx2 : XL.length ≤ 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxc
      simp only [XL]
      omega
    show (XL.map f).toFinset.card ≤ 2
    omega
  have hPmem : ∀ gv ∈ L1 ++ L2, gv.2 = pw p → f gv ∈ P := by
    intro gv hgv hpv
    simp only [P, XL, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨gv, ⟨hgv, hpv⟩, rfl⟩
  have hfalse := hsound P {l} hPcard (by simp) (by
    intro p3 hp3 l3 hl3
    rw [Finset.mem_singleton] at hl3
    subst hl3
    simp only [P, XL, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp3
    obtain ⟨gv, ⟨hgv, hpv⟩, rfl⟩ := hp3
    exact (hf gv hgv hpv).2)
  set z : Fin n → Bool := fun k3 : Fin n =>
    decide (k3.val ∈ P.image pw ∪ ({l} : Finset (Fin M)).image lw) with hz
  have hx : (List.ofFn z).length = n := List.length_ofFn
  have hin : ∀ v (hv : v < n), V C (List.ofFn z) v = z ⟨v, hv⟩ := by
    intro v hv
    rw [V_input C _ v (by rw [hx]; exact hv), List.getD_eq_getElem _ _ (by rw [hx]; exact hv),
      List.getElem_ofFn]
  -- the tree predicate: leaves are reached inputs, and true leaves make the top true
  let Q : ℕ → List (ℕ × ℕ) → Prop := fun t K =>
    (∀ e ∈ K, Reach n C e.2 e.1 ∧ e.2 < n) ∧
      ((∀ e ∈ K, V C (List.ofFn z) e.1 = true) → V C (List.ofFn z) t = true)
  have leaf : ∀ (qv qt : ℕ), qv < n → Reach n C qv qt → Q qt [(qt, qv)] := by
    intro qv qt hqv hR
    refine ⟨?_, fun h => h _ (List.mem_singleton_self _)⟩
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact ⟨hR, hqv⟩
  have node : ∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      Reach n C (n + qj) qt →
      Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 →
      Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 →
      Q qt (qL1 ++ qL2) := by
    intro qj qt qL1 qL2 hqj hop hR hQ1 hQ2
    refine ⟨fun e he => ?_, fun h => ?_⟩
    · rcases List.mem_append.mp he with he | he
      · exact hQ1.1 e he
      · exact hQ2.1 e he
    · have v1 := hQ1.2 fun e he => h e (List.mem_append_left _ he)
      have v2 := hQ2.2 fun e he => h e (List.mem_append_right _ he)
      exact V_reach n C _ hx hrb hR (V_and n C _ hx hrb h2 qj hqj hop v1 v2)
  have hQ1 : Q _ L1 := hT1 Q leaf node
  have hQ2 : Q _ L2 := hT2 Q leaf node
  have hQ := node j0 C.output L1 L2 hj0 hop0 hr0 hQ1 hQ2
  have htrue : V C (List.ofFn z) C.output = true := by
    apply hQ.2
    intro e he
    obtain ⟨hRe, -⟩ := hQ.1 e he
    rcases hside e he with h | h
    · refine V_reach n C _ hx hrb (hf e he h).1 ?_
      rw [hin _ (hpn _), hz]
      simp only [decide_eq_true_eq, Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨f e, hPmem e he h, rfl⟩
    · have hR' : Reach n C (lw l) e.1 := h ▸ hRe
      refine V_reach n C _ hx hrb hR' ?_
      rw [hin _ (hln _), hz]
      simp
  have : PEqualNP.MetaComplexity.circuitFun n C z = true := htrue
  rw [this] at hfalse
  exact Bool.noConfusion hfalse
