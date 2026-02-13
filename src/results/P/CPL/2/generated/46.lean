

theorem P3_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) : Topology.P3 (X:=X) (closure A) := by
  -- Unfold the definition of `P3`
  unfold Topology.P3
  intro x hx
  -- Every point lies in `univ`
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  -- Rewrite using `h.closure_eq` and simplify
  simpa [h.closure_eq, closure_closure, interior_univ] using hx_univ