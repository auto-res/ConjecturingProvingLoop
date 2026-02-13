

theorem Topology.isOpen_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = A → IsOpen (A : Set X) := by
  intro h
  have : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa [h] using this