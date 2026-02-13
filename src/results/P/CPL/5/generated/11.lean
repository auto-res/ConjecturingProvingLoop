

theorem P2_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 (Aᶜ) := by
  simpa using (P2_of_open (A := Aᶜ) hA.isOpen_compl)