

theorem Topology.interior_inter_interiors_eq_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (interior A ∩ interior B) = interior A ∩ interior B := by
  have hA : IsOpen (interior A) := isOpen_interior
  have hB : IsOpen (interior B) := isOpen_interior
  simpa using
    (Topology.interior_inter_eq_of_isOpen (A := interior A) (B := interior B) hA hB)