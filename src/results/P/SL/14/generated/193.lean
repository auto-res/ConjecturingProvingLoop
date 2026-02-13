

theorem Topology.P1_iff_P3_of_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  -- `interior A` is an open set.
  have hOpen : IsOpen (interior A) := isOpen_interior
  -- Apply the existing equivalence for open sets.
  simpa using
    (Topology.P1_iff_P3_of_isOpen (X := X) (A := interior A) hOpen)