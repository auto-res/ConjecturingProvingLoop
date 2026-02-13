

theorem P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3cl
  dsimp [Topology.P3] at hP3cl ⊢
  intro x hx
  -- `x` belongs to the closure of `A`.
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hx
  -- Use `P3` for `closure A` to obtain the desired inclusion.
  have hIncl : closure (A : Set X) ⊆ interior (closure A) := by
    simpa [closure_closure] using hP3cl
  exact hIncl hx_closure