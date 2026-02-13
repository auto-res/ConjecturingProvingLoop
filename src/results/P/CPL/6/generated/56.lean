

theorem P2_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = A) : P2 A := by
  have hA_open : IsOpen (A : Set X) := by
    simpa [h] using (isOpen_interior : IsOpen (interior A))
  simpa using (P2_of_open (A := A) hA_open)