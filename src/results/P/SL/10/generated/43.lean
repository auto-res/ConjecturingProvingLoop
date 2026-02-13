

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  have h_eq :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  simpa [h_eq] using hx