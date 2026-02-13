

theorem Topology.interiorClosureInterior_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  simpa using
    (Topology.interiorClosureInterior_mono
      (A := A) (B := closure A) (subset_closure : (A : Set X) ⊆ closure A))