

theorem denseInterior_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have h_closure : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure] using this