

theorem Topology.frontier_eq_empty_iff_isOpen_and_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = (∅ : Set X) ↔ (IsOpen A ∧ IsClosed A) := by
  constructor
  · intro h
    exact
      Topology.isOpen_and_isClosed_of_frontier_eq_empty
        (X := X) (A := A) h
  · rintro ⟨hOpen, hClosed⟩
    exact
      Topology.frontier_eq_empty_of_isOpen_and_isClosed
        (X := X) (A := A) hOpen hClosed