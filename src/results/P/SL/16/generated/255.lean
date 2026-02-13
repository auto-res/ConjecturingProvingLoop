

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hxInt
  -- A point in the interior of `A` certainly lies in `A`.
  have hxA : (x : X) ∈ A := interior_subset hxInt
  -- Every point of `A` is in the closure of `A`.
  exact subset_closure hxA