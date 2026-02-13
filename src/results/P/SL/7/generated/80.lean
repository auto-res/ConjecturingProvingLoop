

theorem Topology.interior_subset_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ⊆ interior (closure A) := by
  simpa using interior_mono (subset_closure : (A : Set X) ⊆ closure A)