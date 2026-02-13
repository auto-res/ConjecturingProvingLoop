

theorem open_closure_interior_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P1 (closure (interior A))
      ∧ Topology.P2 (closure (interior A))
      ∧ Topology.P3 (closure (interior A)) := by
  simpa using
    Topology.open_satisfies_all_Ps
      (A := closure (interior (A : Set X))) hOpen