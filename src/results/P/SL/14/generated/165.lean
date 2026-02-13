

theorem Topology.interiorClosureInteriorClosure_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) ⊆ interior (closure A) := by
  simpa [closure_closure] using
    (Topology.interiorClosureInterior_subset_interiorClosure
      (X := X) (A := closure A))