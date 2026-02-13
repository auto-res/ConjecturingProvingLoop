

theorem closure_interior_closure_interior_closure_interior_has_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior (closure A))))) := by
  -- The set `interior (closure (interior (closure A)))` already has `P1`.
  have hInner :
      Topology.P1 (interior (closure (interior (closure A)))) :=
    Topology.interior_has_P1
      (X := X) (A := closure (interior (closure A)))
  -- Transfer `P1` through the closure operator.
  exact
    Topology.P1_implies_P1_closure
      (X := X)
      (A := interior (closure (interior (closure A))))
      hInner