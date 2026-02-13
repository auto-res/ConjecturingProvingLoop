

theorem Topology.isOpen_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P3 (X := X) A := by
  simpa [Topology.P3]
    using interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA