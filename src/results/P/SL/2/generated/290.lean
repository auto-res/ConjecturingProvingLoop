

theorem Topology.dense_interior_implies_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 (closure (interior A)) := by
  intro hDense
  intro x hx
  -- Using density, the closure of `interior A` is the whole space.
  have hCl : closure (interior (A : Set X)) = (Set.univ : Set X) := hDense.closure_eq
  -- Rewrite the goal via this equality; everything reduces to `x ∈ univ`.
  have : x ∈ (Set.univ : Set X) := by
    simpa [hCl] using hx
  simpa [hCl, interior_univ, closure_closure] using this