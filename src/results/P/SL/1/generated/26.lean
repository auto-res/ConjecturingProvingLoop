

theorem Topology.P1_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = closure (interior A)) :
    Topology.P1 A := by
  dsimp [Topology.P1] at *
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  simpa [h] using hx_closure