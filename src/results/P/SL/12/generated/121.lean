

theorem Topology.P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure (A : Set X))) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  exact Topology.subset_interior_closure_of_isOpen_closure (X := X) (A := A) h