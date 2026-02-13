

theorem closed_P3_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsOpen A := by
  have hcl : closure A = A := hA_closed.closure_eq
  have hsubset : A ⊆ interior A := by
    dsimp [Topology.P3] at hP3
    simpa [hcl] using hP3
  have hint : interior A ⊆ A := interior_subset
  have heq : interior A = A := Set.Subset.antisymm hint hsubset
  have : IsOpen (interior A) := isOpen_interior
  simpa [heq] using this