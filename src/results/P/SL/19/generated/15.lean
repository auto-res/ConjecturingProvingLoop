

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 (A := A) ↔ IsOpen A := by
  constructor
  · intro hP3
    have hsubset1 : interior A ⊆ A := interior_subset
    have hsubset2 : A ⊆ interior A := by
      have h : A ⊆ interior (closure A) := hP3
      simpa [hA.closure_eq] using h
    have hEq : interior A = A := Set.Subset.antisymm hsubset1 hsubset2
    have hIsOpen : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using hIsOpen
  · intro hOpen
    exact Topology.P3_of_isOpen (A := A) hOpen