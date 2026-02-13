

theorem Topology.interiorClosureInterior_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact interior_mono h_closure