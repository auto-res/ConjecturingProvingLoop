

theorem Topology.P1_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P1 (A := A) := by
  intro hDense
  dsimp [Topology.P1]
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    exact Set.mem_univ x
  simpa [hDense] using this