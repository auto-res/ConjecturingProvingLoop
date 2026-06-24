

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro h
  exact fun x hx ↦ (interior_subset) (h hx)