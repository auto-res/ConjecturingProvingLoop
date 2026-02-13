

theorem Topology.interior_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior A ⊆ closure B := by
  intro x hxInt
  -- From `x ∈ interior A`, we obtain `x ∈ A`.
  have hxA : x ∈ A := interior_subset hxInt
  -- Use the given inclusion `A ⊆ B` to get `x ∈ B`.
  have hxB : x ∈ B := hAB hxA
  -- Every point of `B` lies in `closure B`.
  exact subset_closure hxB