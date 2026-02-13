

theorem interior_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  have hA : IsOpen (interior A) := isOpen_interior
  simpa using Topology.isOpen_imp_P3 hA