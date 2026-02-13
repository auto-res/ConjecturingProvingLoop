

theorem dense_points_mem_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → ∀ x : X, x ∈ closure A := by
  intro hDense x
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Trivially, every point belongs to `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with `h_closure` gives the desired membership.
  simpa [h_closure] using hx_univ