

theorem P3_closed_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A → Topology.P2 A := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P2]
  intro x hxA
  -- From `P3`, `x` lies in `interior (closure A)`, but since `A` is closed,
  -- this is just `interior A`.
  have hx_intA : x ∈ interior A := by
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hA.closure_eq] using this
  -- `interior A` is contained in `interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) :=
    interior_subset_interior_closure_interior
  exact h_subset hx_intA