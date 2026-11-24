import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2676_aux

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

/-- The set of a new gate, as in `readVectors`. -/
def gval (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def rstep (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [gval S k R g]

theorem rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (rstep S k) ((List.range n).map (leafVectors S k)) := rfl

theorem rfold_length (S : List ℕ) (k : ℕ) : ∀ (gs : List Gate) (R : List (List (List ℕ))),
    (gs.foldl (rstep S k) R).length = R.length + gs.length
  | [], R => by simp
  | g :: gs, R => by
    rw [List.foldl_cons, rfold_length S k gs]
    simp [rstep]; omega

theorem rfold_getD_lt (S : List ℕ) (k : ℕ) : ∀ (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ),
    i < R.length → (gs.foldl (rstep S k) R).getD i [] = R.getD i []
  | [], R, i, _ => rfl
  | g :: gs, R, i, hi => by
    rw [List.foldl_cons, rfold_getD_lt S k gs _ i (by simp [rstep]; omega)]
    simp only [rstep]
    rw [List.getD_append _ _ _ _ hi]

/-! Membership in the set operations. -/

theorem mem_foldl_insertNew (x : List ℕ) : ∀ (L A : List (List ℕ)),
    x ∈ L.foldl insertNew A ↔ x ∈ A ∨ x ∈ L
  | [], A => by simp
  | v :: L, A => by
    rw [List.foldl_cons, mem_foldl_insertNew x L]
    unfold insertNew
    split_ifs with h
    · constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · rintro (h1 | h1)
        · exact Or.inl h1
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact Or.inl h
          · exact Or.inr h1
    · simp only [List.mem_append, List.mem_singleton, List.mem_cons]
      tauto

theorem mem_orfold (x : List ℕ) : ∀ (ins : List (List (List ℕ))) (acc : List (List ℕ)),
    x ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ x ∈ acc ∨ ∃ A ∈ ins, x ∈ A
  | [], acc => by simp
  | A :: ins, acc => by
    rw [List.foldl_cons, mem_orfold x ins, mem_foldl_insertNew]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_andStep (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = capAdd k a b := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

/-! Valid vectors and domination. -/

def Val (S : List ℕ) (k : ℕ) (v : List ℕ) : Prop := v.length = S.length ∧ ∀ x ∈ v, x ≤ k + 1

def Dom (w v : List ℕ) : Prop := w.length = v.length ∧ ∀ i, i < v.length → w.getD i 0 ≤ v.getD i 0

theorem dom_refl (v : List ℕ) : Dom v v := ⟨rfl, fun _ _ => le_rfl⟩

theorem getD_le_of_val (S : List ℕ) (k : ℕ) (v : List ℕ) (hv : Val S k v) (i : ℕ) :
    v.getD i 0 ≤ k + 1 := by
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem _ _ hi]; exact hv.2 _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; omega

theorem capAdd_length (k : ℕ) (a b : List ℕ) : (capAdd k a b).length = min a.length b.length := by
  simp [capAdd]

theorem capAdd_getD (k : ℕ) (a b : List ℕ) (i : ℕ) (hi : i < min a.length b.length) :
    (capAdd k a b).getD i 0 = min (a.getD i 0 + b.getD i 0) (k + 1) := by
  rw [List.getD_eq_getElem _ _ (by rw [capAdd_length]; exact hi),
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  simp [capAdd]

theorem val_capAdd (S : List ℕ) (k : ℕ) (a b : List ℕ) (ha : Val S k a) (hb : Val S k b) :
    Val S k (capAdd k a b) := by
  refine ⟨by rw [capAdd_length, ha.1, hb.1, min_self], fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := capAdd_getD k a b i (by rw [capAdd_length] at hi; exact hi)
  rw [List.getD_eq_getElem _ _ hi] at this
  rw [this]; exact min_le_right _ _

theorem dom_capAdd_left (S : List ℕ) (k : ℕ) (w a b : List ℕ) (hw : Val S k w) (ha : Val S k a)
    (hb : Val S k b) (h : Dom w a) : Dom w (capAdd k a b) := by
  have hl : (capAdd k a b).length = S.length := by rw [capAdd_length, ha.1, hb.1, min_self]
  refine ⟨by rw [hl, hw.1], fun i hi => ?_⟩
  rw [hl] at hi
  rw [capAdd_getD k a b i (by rw [ha.1, hb.1, min_self]; exact hi)]
  have h1 := h.2 i (by rw [ha.1]; exact hi)
  have h2 := getD_le_of_val S k w hw i
  omega

theorem capAdd_comm (k : ℕ) (a b : List ℕ) : capAdd k a b = capAdd k b a := by
  unfold capAdd
  rw [List.zipWith_comm]
  congr 1
  funext x y
  rw [Nat.add_comm]

theorem good_of_dom (k : ℕ) (w v : List ℕ) (h : Dom w v)
    (hv : (v.all fun a => decide (a ≤ k)) = true) : (w.all fun a => decide (a ≤ k)) = true := by
  rw [List.all_eq_true] at hv ⊢
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have h1 := h.2 i (by rw [← h.1]; exact hi)
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by rw [← h.1]; exact hi)] at h1
  have h2 := hv _ (List.getElem_mem (by rw [← h.1]; exact hi))
  simp only [decide_eq_true_eq] at h2 ⊢
  omega

/-! Validity of all sets. -/

def AllVal (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) : Prop :=
  ∀ i, ∀ v ∈ R.getD i [], Val S k v

theorem val_andfold (S : List ℕ) (k : ℕ) : ∀ (As : List (List (List ℕ))) (X : List (List ℕ)),
    (∀ v ∈ X, Val S k v) → (∀ A ∈ As, ∀ v ∈ A, Val S k v) →
    ∀ v ∈ As.foldl (andStep k) X, Val S k v
  | [], X, hX, _ => hX
  | A :: As, X, hX, hAs => by
    rw [List.foldl_cons]
    apply val_andfold S k As
    · intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_andStep k X A v).mp hv
      exact val_capAdd S k a b (hX a ha) (hAs A (List.mem_cons_self ..) b hb)
    · exact fun A' hA' => hAs A' (List.mem_cons_of_mem _ hA')

theorem val_gval (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (hR : AllVal S k R) (g : Gate) :
    ∀ v ∈ gval S k R g, Val S k v := by
  have hins : ∀ A ∈ g.inputs.map (fun i => R.getD i []), ∀ v ∈ A, Val S k v := by
    intro A hA v hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hA
    exact hR i v hv
  unfold gval
  intro v hv
  split at hv
  · obtain hv | ⟨A, hA, hv⟩ := (mem_orfold v _ []).mp hv
    · simp at hv
    · exact hins A hA v hv
  · refine val_andfold S k _ _ ?_ hins v hv
    intro w hw
    rw [List.mem_singleton] at hw
    subst hw
    exact ⟨by simp, by simp⟩
  · simp at hv

theorem val_rstep (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (hR : AllVal S k R) (g : Gate) :
    AllVal S k (rstep S k R g) := by
  intro i v hv
  unfold rstep at hv
  rcases lt_trichotomy i R.length with hi | rfl | hi
  · rw [List.getD_append _ _ _ _ hi] at hv; exact hR i v hv
  · rw [List.getD_append_right _ _ _ _ le_rfl] at hv
    simp only [Nat.sub_self, List.getD_cons_zero] at hv
    exact val_gval S k R hR g v hv
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hv; simp at hv

theorem val_rfold (S : List ℕ) (k : ℕ) : ∀ (gs : List Gate) (R : List (List (List ℕ))),
    AllVal S k R → AllVal S k (gs.foldl (rstep S k) R)
  | [], _, h => h
  | g :: gs, R, h => val_rfold S k gs _ (val_rstep S k R h g)

theorem val_init (S : List ℕ) (k n : ℕ) : AllVal S k ((List.range n).map (leafVectors S k)) := by
  intro i v hv
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)] at hv
    simp only [List.getElem_map, List.getElem_range, leafVectors] at hv
    split_ifs at hv
    · rw [List.mem_singleton] at hv
      subst hv
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [List.mem_map] at hx
      obtain ⟨j, -, rfl⟩ := hx
      split_ifs <;> omega
    · simp at hv
  · rw [List.getD_eq_default _ _ (by simpa using hi)] at hv; simp at hv

/-! The relation between old and lifted sets. -/

/-- Every old vector is a lifted vector or dominates a vector of `T`. -/
def Rel (T : List (List ℕ)) (X Y : List (List ℕ)) : Prop :=
  ∀ v ∈ X, v ∈ Y ∨ ∃ w ∈ T, Dom w v

theorem rel_andfold (S : List ℕ) (k : ℕ) (T : List (List ℕ)) (hT : ∀ w ∈ T, Val S k w) :
    ∀ (As Bs : List (List (List ℕ))) (X Y : List (List ℕ)), As.length = Bs.length →
    (∀ v ∈ X, Val S k v) → (∀ A ∈ As, ∀ v ∈ A, Val S k v) → Rel T X Y →
    (∀ i (h1 : i < As.length) (h2 : i < Bs.length), Rel T As[i] Bs[i]) →
    Rel T (As.foldl (andStep k) X) (Bs.foldl (andStep k) Y)
  | [], [], X, Y, _, _, _, hXY, _ => hXY
  | A :: As, B :: Bs, X, Y, hl, hX, hAs, hXY, hAB => by
    rw [List.foldl_cons, List.foldl_cons]
    have hA : ∀ v ∈ A, Val S k v := hAs A (List.mem_cons_self ..)
    apply rel_andfold S k T hT As Bs _ _ (by simpa using hl)
    · intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_andStep k X A v).mp hv
      exact val_capAdd S k a b (hX a ha) (hA b hb)
    · exact fun A' hA' => hAs A' (List.mem_cons_of_mem _ hA')
    · intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_andStep k X A v).mp hv
      have hAB0 := hAB 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at hAB0
      rcases hXY a ha with ha' | ⟨w, hw, hwa⟩
      · rcases hAB0 b hb with hb' | ⟨w, hw, hwb⟩
        · exact Or.inl ((mem_andStep k Y B _).mpr ⟨a, ha', b, hb', rfl⟩)
        · right
          refine ⟨w, hw, ?_⟩
          rw [capAdd_comm]
          exact dom_capAdd_left S k w b a (hT w hw) (hA b hb) (hX a ha) hwb
      · exact Or.inr ⟨w, hw, dom_capAdd_left S k w a b (hT w hw) (hX a ha) (hA b hb) hwa⟩
    · intro i h1 h2
      have := hAB (i + 1) (by simpa using h1) (by simpa using h2)
      simpa using this
  | [], _ :: _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _, _ => by simp at hl

/-- The invariant of the two runs after the changed gate. -/
def Sim (S : List ℕ) (k : ℕ) (T : List (List ℕ)) (Ro Rl : List (List (List ℕ))) : Prop :=
  Ro.length = Rl.length ∧ AllVal S k Ro ∧ ∀ i, Rel T (Ro.getD i []) (Rl.getD i [])

theorem sim_rstep (S : List ℕ) (k : ℕ) (T : List (List ℕ)) (hT : ∀ w ∈ T, Val S k w)
    (Ro Rl : List (List (List ℕ))) (h : Sim S k T Ro Rl) (g : Gate) :
    Sim S k T (rstep S k Ro g) (rstep S k Rl g) := by
  obtain ⟨hl, hval, hrel⟩ := h
  have hnew : Rel T (gval S k Ro g) (gval S k Rl g) := by
    unfold gval
    split
    · intro v hv
      obtain hv | ⟨A, hA, hv⟩ := (mem_orfold v _ []).mp hv
      · simp at hv
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
        rcases hrel i v hv with hv' | hd
        · exact Or.inl ((mem_orfold v _ []).mpr (Or.inr ⟨_, List.mem_map_of_mem hi, hv'⟩))
        · exact Or.inr hd
    · apply rel_andfold S k T hT _ _ _ _ (by simp)
      · intro w hw; rw [List.mem_singleton] at hw; subst hw; exact ⟨by simp, by simp⟩
      · intro A hA v hv
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hA
        exact hval i v hv
      · intro v hv; exact Or.inl hv
      · intro i h1 h2
        simp only [List.getElem_map]
        exact hrel _
    · intro v hv; simp at hv
  refine ⟨by simp [rstep, hl], val_rstep S k Ro hval g, fun i => ?_⟩
  unfold rstep
  rcases lt_trichotomy i Ro.length with hi | rfl | hi
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]; exact hrel i
  · rw [List.getD_append_right _ _ _ _ le_rfl, hl, List.getD_append_right _ _ _ _ le_rfl]
    simpa using hnew
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro v hv; simp at hv

theorem sim_rfold (S : List ℕ) (k : ℕ) (T : List (List ℕ)) (hT : ∀ w ∈ T, Val S k w) :
    ∀ (gs : List Gate) (Ro Rl : List (List (List ℕ))), Sim S k T Ro Rl →
      Sim S k T (gs.foldl (rstep S k) Ro) (gs.foldl (rstep S k) Rl)
  | [], _, _, h => h
  | g :: gs, Ro, Rl, h => sim_rfold S k T hT gs _ _ (sim_rstep S k T hT Ro Rl h g)

theorem main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∀ (S : List ℕ) (k : ℕ), PEqualNP.ReadK.readsAtMost C n S k = true → PEqualNP.ReadK.readsAtMost { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } n S k = true := by
  intro n C j u t _ hj hg ht _ S k hread
  set init := (List.range n).map (leafVectors S k)
  set P := (C.gates.take j).foldl (rstep S k) init with hP
  have hPl : P.length = n + j := by
    rw [hP, rfold_length]; simp [init]; omega
  have hgj : C.gates[j] = { op := GateOp.or, inputs := [u, t] } := by
    rw [List.getElem?_eq_getElem hj] at hg; exact Option.some.inj hg
  set rest := C.gates.drop (j + 1)
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: rest := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  set g' : Gate := { op := GateOp.or, inputs := [u] }
  have hset : C.gates.set j g' = C.gates.take j ++ g' :: rest := by
    rw [List.set_eq_take_append_cons_drop, if_pos hj]
  set T := P.getD t [] with hTdef
  have hPval : AllVal S k P := val_rfold S k _ _ (val_init S k n)
  have hT : ∀ w ∈ T, Val S k w := fun w hw => hPval t w hw
  -- the old run
  have hRo : readVectors C n S k = rest.foldl (rstep S k) (rstep S k P C.gates[j]) := by
    rw [rv_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  -- the lifted run, before its top gate
  have hRl : (C.gates.set j g').foldl (rstep S k) init = rest.foldl (rstep S k) (rstep S k P g') := by
    rw [hset, List.foldl_append, List.foldl_cons]
  -- the two runs after the changed gate
  have hsim0 : Sim S k T (rstep S k P C.gates[j]) (rstep S k P g') := by
    refine ⟨by simp [rstep], val_rstep S k P hPval _, fun i => ?_⟩
    unfold rstep
    rcases lt_trichotomy i P.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
      intro v hv; exact Or.inl hv
    · rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
      simp only [Nat.sub_self, List.getD_cons_zero]
      intro v hv
      rw [hgj] at hv
      simp only [gval, g', List.map_cons, List.map_nil] at hv ⊢
      obtain hv | ⟨A, hA, hv⟩ := (mem_orfold v _ []).mp hv
      · simp at hv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl
        · exact Or.inl ((mem_orfold v _ []).mpr (Or.inr ⟨_, List.mem_singleton_self _, hv⟩))
        · exact Or.inr ⟨v, hv, dom_refl v⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      intro v hv; simp at hv
  obtain ⟨hlen, -, hrel⟩ := sim_rfold S k T hT rest _ _ hsim0
  set Ro := rest.foldl (rstep S k) (rstep S k P C.gates[j])
  set Rl := rest.foldl (rstep S k) (rstep S k P g')
  have hRlt : Rl.getD t [] = T := by
    rw [rfold_getD_lt S k rest _ t (by simp [rstep]; omega)]
    simp only [rstep]
    rw [List.getD_append _ _ _ _ (by omega)]
  have hRll : Rl.length = n + C.gates.length := by
    rw [rfold_length]; simp [rstep, hPl]
    have : rest.length = C.gates.length - (j + 1) := List.length_drop
    omega
  -- read the old output
  unfold readsAtMost at hread ⊢
  rw [hRo, List.any_eq_true] at hread
  obtain ⟨v, hv, hgood⟩ := hread
  rw [rv_eq, List.foldl_append, hRl, List.foldl_cons, List.foldl_nil, List.any_eq_true]
  simp only
  rw [show (rstep S k Rl { op := GateOp.or, inputs := [C.output, t] }).getD
      (n + C.gates.length) [] =
      gval S k Rl { op := GateOp.or, inputs := [C.output, t] } by
    unfold rstep
    rw [← hRll, List.getD_append_right _ _ _ _ le_rfl]
    simp]
  simp only [gval, List.map_cons, List.map_nil]
  rcases hrel C.output v hv with hv' | ⟨w, hw, hwv⟩
  · exact ⟨v, (mem_orfold v _ []).mpr (Or.inr ⟨_, List.mem_cons_self .., hv'⟩), hgood⟩
  · refine ⟨w, (mem_orfold w _ []).mpr (Or.inr ⟨Rl.getD t [], by simp, by rw [hRlt]; exact hw⟩),
      good_of_dom k w v hwv hgood⟩

end PEqualNP.Outside.L_meta_2676_aux

theorem PEqualNP.Outside.L_meta_2676 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∀ (S : List ℕ) (k : ℕ), PEqualNP.ReadK.readsAtMost C n S k = true → PEqualNP.ReadK.readsAtMost { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } n S k = true := by
  exact PEqualNP.Outside.L_meta_2676_aux.main
