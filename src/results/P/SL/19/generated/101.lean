

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- Using the previously proved equality of closures
  have hEq :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  -- Rewrite `hx` via `hEq` to obtain the required membership
  have : x ∈ closure (interior (closure (interior A))) := by
    simpa [hEq] using hx
  exact this