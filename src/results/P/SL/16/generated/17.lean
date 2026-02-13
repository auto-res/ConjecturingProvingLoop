

theorem Topology.interior_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior A) ∧
    Topology.P2 (X := X) (interior A) ∧
    Topology.P3 (X := X) (interior A) := by
  exact
    ⟨Topology.P1_interior (X := X) (A := A),
      Topology.P2_interior (X := X) (A := A),
      Topology.P3_interior (X := X) (A := A)⟩