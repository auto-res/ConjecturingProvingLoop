

theorem Topology.dense_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P2 (closure (A : Set X)) := by
  intro hDense
  intro x hx
  -- Since `A` is dense, `closure A = univ`, so `x` is trivially in `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [hDense.closure_eq] using hx
  -- Unravel the goal using the fact that every set equals `univ`.
  simpa [hDense.closure_eq, interior_univ, closure_univ] using hx_univ