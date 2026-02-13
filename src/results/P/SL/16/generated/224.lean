

theorem IsClosed.compl {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : IsOpen Aᶜ := by
  simpa [isOpen_compl_iff] using (isOpen_compl_iff).2 hA