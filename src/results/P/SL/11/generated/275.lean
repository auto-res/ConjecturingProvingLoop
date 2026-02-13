

theorem closed_eq_univ_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : closure (A : Set X) = (Set.univ : Set X)) :
    A = (Set.univ : Set X) := by
  simpa [hClosed.closure_eq] using hDense