

theorem P3_iff_open_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    have hsubset : (A : Set X) ⊆ interior A := by
      -- Rewrite `interior (closure A)` using `hA.closure_eq`.
      have h : (A : Set X) ⊆ interior (closure A) := hP3
      simpa [hA.closure_eq] using h
    have hEq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact hsubset
    -- Since `interior A` is open, `A` is open as well.
    have : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using this
  · intro hOpen
    exact Topology.P3_of_open (A := A) hOpen