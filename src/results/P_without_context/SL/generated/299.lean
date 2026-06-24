

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : P2 (A := A)) : P1 (A := A) := by
  unfold P1 P2 at *
  exact fun x hx => interior_subset (h hx)