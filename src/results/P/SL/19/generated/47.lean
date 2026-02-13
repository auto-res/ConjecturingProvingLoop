

theorem Topology.interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  have hSub : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal (subset_closure : interior A ⊆ closure (interior A))
      isOpen_interior
  exact hSub hx