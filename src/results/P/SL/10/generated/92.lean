

theorem Topology.P1_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P1 A := by
  intro h_closure
  dsimp [Topology.P1]
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_closure] using this