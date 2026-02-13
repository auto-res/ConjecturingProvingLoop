

theorem closure_compl_eq_self_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    closure (Aᶜ) = Aᶜ := by
  have hClosed : IsClosed (Aᶜ) := hA.isClosed_compl
  simpa using hClosed.closure_eq