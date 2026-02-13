

theorem Topology.P1_of_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = closure (interior A) → Topology.P1 (A := A) := by
  intro hEq
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hEq] using this