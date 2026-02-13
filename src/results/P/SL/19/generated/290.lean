

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  have hEq :=
    Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
      (X := X) (A := A)
  have : x ∈ closure (interior (closure (interior (closure A)))) := by
    simpa [hEq] using hx
  exact this