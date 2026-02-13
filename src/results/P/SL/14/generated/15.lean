

theorem Topology.P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  have h_closure : closure A = A := hA_closed.closure_eq
  constructor
  · intro hP3
    dsimp [Topology.P3] at hP3
    have h1 : (A : Set X) ⊆ interior A := by
      simpa [h_closure] using hP3
    have h2 : interior A ⊆ A := interior_subset
    have h_eq : interior A = A := Set.Subset.antisymm h2 h1
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro hA_open
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hA_open