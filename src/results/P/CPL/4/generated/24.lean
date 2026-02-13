

theorem P1_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior A) : Topology.P1 A := by
  dsimp [P1]
  intro x hx
  -- first, `x` lies in `closure A`
  have hx_cl : x ∈ closure A := subset_closure hx
  -- rewrite using the equality `closure A = interior A`
  have hx_int : x ∈ interior A := by
    simpa [h] using hx_cl
  -- `interior A ⊆ closure (interior A)`
  exact subset_closure hx_int