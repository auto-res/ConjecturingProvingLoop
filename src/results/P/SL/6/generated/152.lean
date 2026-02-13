

theorem closure_interior_closure_interior_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (interior (A : Set X))))) := by
  -- `P1` holds for `interior (closure (interior A))`.
  have hP1 : Topology.P1 (interior (closure (interior (A : Set X)))) :=
    Topology.interior_closure_interior_satisfies_P1 (A := A)
  -- `P1` is stable under taking closures.
  exact
    Topology.P1_closure_of_P1
      (A := interior (closure (interior (A : Set X)))) hP1