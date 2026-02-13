

theorem P1_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P1 (Aᶜ) := by
  exact P1_of_P2 (A := Aᶜ) (P2_compl_of_closed (A := A) hA)