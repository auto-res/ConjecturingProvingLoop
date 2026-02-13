

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  -- Use the previously proven equality of the two closures
  have h_eq :=
    Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
      (X := X) (A := A)
  -- Rewrite `hx` using this equality to obtain the required membership
  simpa [h_eq] using (hx : x ∈ closure (interior (closure A)))