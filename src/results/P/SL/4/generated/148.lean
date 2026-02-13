

theorem dense_interior_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P1 A := by
  intro hDense
  dsimp [Topology.P1]
  intro x hxA
  -- Since `interior A` is dense, its closure is `univ`.
  have h_closure : (closure (interior A) : Set X) = Set.univ := hDense.closure_eq
  -- Every point lies in `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure] using hx_univ