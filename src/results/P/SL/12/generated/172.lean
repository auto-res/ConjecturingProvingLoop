

theorem Topology.P2_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior A) ↔ Topology.P3 (X := X) (interior A) := by
  -- `interior A` is an open set.
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  -- Apply the general equivalence for open sets.
  simpa using
    (Topology.P2_iff_P3_of_isOpen (X := X) (A := interior A) h_open)