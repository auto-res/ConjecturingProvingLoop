

theorem Topology.isOpen_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → interior (closure (interior A)) = interior (closure A) := by
  intro hOpen
  -- Any open set satisfies property `P2`.
  have hP2 : Topology.P2 A := Topology.isOpen_implies_P2 (A := A) hOpen
  -- Apply the equality furnished by `P2`.
  exact
    Topology.P2_implies_interior_closure_interior_eq_interior_closure
      (A := A) hP2