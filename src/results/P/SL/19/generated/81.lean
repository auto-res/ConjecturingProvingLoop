

theorem Topology.interior_eq_empty_of_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure A) = (∅ : Set X)) :
    interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (A := A)) hx
    simpa [h] using this
  · simpa using (Set.empty_subset _)