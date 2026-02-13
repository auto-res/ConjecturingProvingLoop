

theorem P2_interior_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  exact
    Topology.isOpen_implies_P2
      (X := X)
      (A := interior (closure (interior (closure A))))
      h_open