

theorem isClosed_eq_univ_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) → A = (Set.univ : Set X) := by
  intro hDense
  simpa [hA_closed.closure_eq] using hDense