

theorem interior_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    interior ((Aᶜ) : Set X) = Aᶜ := by
  simpa using hA_closed.isOpen_compl.interior_eq