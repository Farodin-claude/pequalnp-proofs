import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3744_aux

open PEqualNP.CircuitLowerBounds

/-- The bits of `m` are the entries of `w`, and `m` has no bit at or above `w.length`. -/
def Enc (w : List Bool) (m : ℕ) : Prop :=
  (∀ i, w.getD i false = m.testBit i) ∧ ∀ i, w.length ≤ i → m.testBit i = false

/-- Set bit `k` of `m` when `b` holds. -/
def put (m k : ℕ) (b : Bool) : ℕ := if b then m ||| 2 ^ k else m

theorem enc_snoc (w : List Bool) (m : ℕ) (b : Bool) (h : Enc w m) :
    Enc (w ++ [b]) (put m w.length b) := by
  obtain ⟨h1, h2⟩ := h
  unfold put
  constructor
  · intro i
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ hi, h1]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow] <;> omega
    · rw [List.getD_append_right _ _ _ _ le_rfl]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow, h2]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      cases b <;> simp [Nat.testBit_or, h2 i hi.le, Nat.testBit_two_pow] <;> omega
  · intro i hi
    simp at hi
    cases b <;> simp [Nat.testBit_or, h2 i (by omega), Nat.testBit_two_pow] <;> omega

/-- Pack a list of bits, the next one at position `k`. -/
def pack : ℕ → ℕ → List Bool → ℕ
  | _, m, [] => m
  | k, m, b :: bs => pack (k + 1) (put m k b) bs

theorem pack_enc : ∀ (bs w : List Bool) (m : ℕ), Enc w m → Enc (w ++ bs) (pack w.length m bs)
  | [], w, m, h => by simpa [pack] using h
  | b :: bs, w, m, h => by
    have := pack_enc bs (w ++ [b]) _ (enc_snoc w m b h)
    simpa [pack] using this

/-- Run the gates on a packed wire vector, the next gate writing bit `k`. -/
def runB : ℕ → ℕ → List Gate → ℕ
  | _, m, [] => m
  | k, m, g :: gs => runB (k + 1) (put m k (g.op.eval (g.inputs.map fun i => m.testBit i))) gs

theorem runB_enc : ∀ (gs : List Gate) (w : List Bool) (m : ℕ), Enc w m →
    Enc (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      (runB w.length m gs)
  | [], w, m, h => by simpa [runB] using h
  | g :: gs, w, m, h => by
    have hmap : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => m.testBit i) :=
      List.map_congr_left (fun i _ => h.1 i)
    have := runB_enc gs _ _ (enc_snoc w m (g.op.eval (g.inputs.map fun i => w.getD i false)) h)
    simp only [List.foldl_cons, runB]
    rw [hmap] at this ⊢
    simpa using this

theorem wires_bits (C : Circuit) (x : List Bool) (i : ℕ) :
    (C.wires x).getD i false = (runB x.length (pack 0 0 x) C.gates).testBit i := by
  have hx := pack_enc x [] 0 ⟨by simp, by simp⟩
  simp only [List.nil_append, List.length_nil] at hx
  exact (runB_enc C.gates x _ hx).1 i

theorem eval_bits (C : Circuit) (x : List Bool) :
    C.eval x = (runB x.length (pack 0 0 x) C.gates).testBit C.output :=
  wires_bits C x C.output

end PEqualNP.Outside.L_meta_3744_aux


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_3744 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 7 C ∧ C.size = 9 ∧
  (∀ x : Fin 7 → Bool, PEqualNP.MetaComplexity.circuitFun 7 C x = decide (∃ e ∈ ([(0, 5), (0, 6), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 5), (0, 6), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), PEqualNP.Core.ReadTwiceAt 7 C (C.output - 7) e.1 e.2 ↔ e ∈ ([(0, 5), (0, 6), (2, 3), (2, 5)] : List (Fin 7 × Fin 7))) := by
  and_intros
  all_goals
    intro C hC
    subst hC
    and_intros
    all_goals first
      | rfl
      | (simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.MetaComplexity.Monotone2]; done)
      | (intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (subst h; simp))
      | (simp only [PEqualNP.Outside.L_meta_3744_aux.eval_bits, PEqualNP.Outside.L_meta_3744_aux.wires_bits]; set_option maxRecDepth 100000 in decide +kernel)
      | decide
      | decide +kernel
