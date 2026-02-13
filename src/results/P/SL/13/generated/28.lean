

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ⊆ interior (closure A) := by
  intro x hx
  exact (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx