

theorem Topology.P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    dsimp [Topology.P3] at hP3
    have hsubset1 : (A : Set X) ⊆ interior A := by
      simpa [hA.closure_eq] using hP3
    have hsubset2 : interior A ⊆ A := interior_subset
    have hEq : interior A = A := Set.Subset.antisymm hsubset2 hsubset1
    have : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using this
  · intro hOpen
    exact Topology.P3_of_isOpen hOpen