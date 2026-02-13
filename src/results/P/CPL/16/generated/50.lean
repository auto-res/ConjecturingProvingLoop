

theorem P2_closed_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → IsClosed A → closure (interior A) = A := by
  intro hP2 hClosed
  have hP1 : P1 A := (P2_subset_P1 (A := A)) hP2
  exact (P1_eq_of_closed (A := A)) hClosed hP1