

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  -- Identify the closure of the interior of our target set with the set itself.
  have h_eq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := closure A)
  -- Rewrite `hx` using the above equality to obtain the desired membership.
  have hx' : x ∈ closure (interior (closure (interior (closure A)))) := by
    simpa [h_eq] using hx
  exact hx'