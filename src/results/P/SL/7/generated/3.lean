

theorem IsOpen_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A := by
  simpa [Topology.P2, hA.interior_eq] using interior_maximal subset_closure hA