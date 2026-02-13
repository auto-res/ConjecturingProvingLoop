

theorem Topology.isClosed_P3_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → Topology.P1 A := by
  intro hClosed hP3
  intro x hxA
  -- From `P3`, `x` is in the interior of `closure A`, but since `A` is closed,
  -- `closure A = A`, so `x` is in `interior A`.
  have hx_int : x ∈ interior A := by
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hClosed.closure_eq] using this
  -- Any point of `interior A` is certainly in `closure (interior A)`.
  exact subset_closure hx_int