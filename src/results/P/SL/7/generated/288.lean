

theorem Topology.interior_subset_closure_of_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ⊆ closure (interior A) := by
  intro x hx
  exact subset_closure hx