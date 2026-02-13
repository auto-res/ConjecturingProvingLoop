

theorem Topology.innerInterior_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure A) := by
  intro x hx
  exact (interior_mono (subset_closure : A ⊆ closure A)) hx