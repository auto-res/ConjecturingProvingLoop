

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → closure A = Set.univ → P2 A := by
  intro hClosed hDense
  have hA_univ : (A : Set X) = Set.univ := by
    have hCl : closure A = A := hClosed.closure_eq
    simpa [hCl] using hDense
  simpa [hA_univ] using (P2_univ : P2 (Set.univ : Set X))

theorem P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → closure A = Set.univ → P1 A := by
  intro hClosed hDense
  have hA_univ : (A : Set X) = Set.univ := by
    simpa [hClosed.closure_eq] using hDense
  simpa [hA_univ] using (P1_univ : P1 (Set.univ : Set X))