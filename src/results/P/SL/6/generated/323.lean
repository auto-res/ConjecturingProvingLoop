

theorem open_closure_interior_iff_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (interior (A : Set X))) ↔
      (Topology.P1 (closure (interior A)) ∧
        Topology.P2 (closure (interior A)) ∧
        Topology.P3 (closure (interior A))) := by
  constructor
  · intro hOpen
    simpa using
      (Topology.open_closure_interior_satisfies_all_Ps
        (A := A) hOpen)
  · rintro ⟨_, _, hP3⟩
    exact
      ((Topology.P3_closure_interior_iff_open_closure_interior
        (A := A)).1 hP3)