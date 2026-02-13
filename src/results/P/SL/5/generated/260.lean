

theorem IsClosed.isOpen_compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsClosed (s : Set X)) : IsOpen ((s : Set X)ᶜ) := by
  simpa using (isOpen_compl_iff).2 h