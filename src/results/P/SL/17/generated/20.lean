

theorem Topology.isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) : IsOpen A := by
  have h_subset : A ⊆ interior A := by
    intro x hx
    have : x ∈ interior (closure A) := hP3 hx
    simpa [hA_closed.closure_eq] using this
  have h_eq : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    · exact h_subset
  simpa [h_eq] using (isOpen_interior : IsOpen (interior A))