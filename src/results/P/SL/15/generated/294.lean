

set_option maxRecDepth 1000

theorem dense_implies_P3_interior_closure_fixed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (interior (closure A)) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Consequently, the interior of this closure is also the whole space.
  have h_int_closure : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  -- The claim now follows trivially.
  simpa [h_int_closure] using (trivial : x ∈ (Set.univ : Set X))