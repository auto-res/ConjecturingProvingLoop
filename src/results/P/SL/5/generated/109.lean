

theorem P3_interior_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (X := X) (interior (closure (interior (closure A)))) := by
  -- The interior of any set is open.
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  -- Hence it satisfies `P3`.
  exact
    Topology.isOpen_implies_P3
      (X := X)
      (A := interior (closure (interior (closure A))))
      h_open