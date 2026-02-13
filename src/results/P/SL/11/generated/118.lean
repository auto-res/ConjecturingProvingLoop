

theorem P123_of_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) ∧
      Topology.P2 (interior (closure A)) ∧
      Topology.P3 (interior (closure A)) := by
  exact
    ⟨Topology.P1_of_interior_closure (A := A),
      Topology.P2_of_interior_closure (A := A),
      Topology.P3_of_interior_closure (A := A)⟩