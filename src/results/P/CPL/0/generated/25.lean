

theorem P1_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Dense A → P1 A := by
  intro hClosed hDense
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
      (dense_iff_closure_eq).1 hDense
    have h_closure_eq : closure (A : Set X) = A := hClosed.closure_eq
    simpa [h_closure_eq] using h_closure
  simpa [hA_univ] using (P1_univ : P1 (Set.univ : Set X))