

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → Topology.P1 A := by
  intro hClosed hP3
  intro x hxA
  -- `P3` gives that `x` is in the interior of `closure A`, but `closure A = A` since `A` is closed.
  have hxInt : x ∈ interior A := by
    simpa [hClosed.closure_eq] using (hP3 hxA)
  -- Any point of `interior A` lies in `closure (interior A)`.
  exact subset_closure hxInt