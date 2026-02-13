

theorem subset_interiorClosure_of_subset_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP3B : Topology.P3 B) :
    A ⊆ interior (closure B) := by
  intro x hxA
  -- Since `A ⊆ B`, the point `x` belongs to `B`.
  have hxB : x ∈ B := hAB hxA
  -- Apply the `P3` property of `B`.
  exact hP3B hxB