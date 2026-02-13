

theorem P123_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧
      Topology.P2 (interior A) ∧
      Topology.P3 (interior A) := by
  exact
    ⟨Topology.P1_of_interior (A := A),
      Topology.P2_of_interior (A := A),
      Topology.P3_of_interior (A := A)⟩