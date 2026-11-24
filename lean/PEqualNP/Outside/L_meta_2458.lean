import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2458_aux

open Configuration

instance fact211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

/-- The projective plane over the field with 211 elements (points and lines alike). -/
abbrev Pt := Projectivization (ZMod 211) (Fin 3 → ZMod 211)

noncomputable instance : Fintype Pt := Fintype.ofFinite _

theorem natCard_Pt : Nat.card Pt = 211 ^ 2 + 211 + 1 := by
  rw [Projectivization.card_of_finrank (ZMod 211) (Fin 3 → ZMod 211) (Module.finrank_fin_fun _)]
  simp [Finset.sum_range_succ, Nat.card_eq_fintype_card, ZMod.card]

theorem order_eq : ProjectivePlane.order Pt Pt = 211 := by
  have h1 := ProjectivePlane.card_points Pt Pt
  rw [Fintype.card_eq_nat_card, natCard_Pt] at h1
  set q := ProjectivePlane.order Pt Pt
  have hle : q ≤ 211 := by nlinarith
  have hge : 211 ≤ q := by nlinarith
  omega

theorem main : ∃ (x1 : ℕ) (x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3),
    (201 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧
    (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) ∧
    ∀ (x5 x6 : Fin x2), x5 ≠ x6 → ∃! x8 : Fin x2, x3 x5 x8 ∧ x3 x6 x8 := by
  classical
  let e : Fin (Fintype.card Pt) ≃ Pt := (Fintype.equivFin Pt).symm
  refine ⟨ProjectivePlane.order Pt Pt, Fintype.card Pt, fun i j => e i ∈ e j,
    fun _ _ => Classical.dec _, ?_, ProjectivePlane.card_points Pt Pt, ?_, ?_⟩
  · rw [order_eq]; norm_num
  · intro j
    rw [← ProjectivePlane.pointCount_eq Pt (e j), pointCount, ← Fintype.card_eq_nat_card]
    exact Fintype.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
  · intro i i' hii
    have hne : e i ≠ e i' := fun h => hii (e.injective h)
    obtain ⟨l, hl, hu⟩ := HasLines.existsUnique_line Pt Pt (e i) (e i') hne
    refine ⟨e.symm l, ?_, fun y hy => ?_⟩
    · simpa using hl
    · have := hu (e y) hy
      rw [← this, Equiv.symm_apply_apply]

end PEqualNP.Outside.L_meta_2458_aux

theorem PEqualNP.Outside.L_meta_2458 : ∃ (x1 : ℕ) (x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3), (201 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧ (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) ∧ ∀ (x5 x6 : Fin x2), x5 ≠ x6 → ∃! x8 : Fin x2, x3 x5 x8 ∧ x3 x6 x8 := by
  exact PEqualNP.Outside.L_meta_2458_aux.main
