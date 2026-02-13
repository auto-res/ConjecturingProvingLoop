

theorem Topology.interior_inter_interior_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ interior B) = interior A ∩ interior B := by
  have hOpen : IsOpen (interior B) := isOpen_interior
  simpa using
    (Topology.interior_inter_open_right (X := X) (A := A) (B := interior B) hOpen)