

theorem interior_closure_interior_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A)))
      ∧ Topology.P2 (interior (closure (interior A)))
      ∧ Topology.P3 (interior (closure (interior A))) := by
  exact
    ⟨Topology.interior_closure_interior_satisfies_P1 (A := A),
      Topology.interior_closure_interior_satisfies_P2 (A := A),
      Topology.interior_closure_interior_satisfies_P3 (A := A)⟩