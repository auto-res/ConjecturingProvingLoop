

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  exact P2_subset_P1 (P2_self (A := A))