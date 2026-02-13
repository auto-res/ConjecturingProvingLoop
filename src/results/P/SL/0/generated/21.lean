

theorem P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 A ↔ IsOpen (A : Set X) := by
  dsimp [Topology.P3]
  have h_closure : closure (A : Set X) = A := hA.closure_eq
  constructor
  · intro hP3
    have h_subset : (A : Set X) ⊆ interior A := by
      simpa [h_closure] using hP3
    have h_eq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact h_subset
    simpa [h_eq] using
      (isOpen_interior : IsOpen (interior (A : Set X)))
  · intro hOpen
    exact (Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen).2.2