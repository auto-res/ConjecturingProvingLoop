

theorem Topology.interiorClosure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :
        interior (closure (interior (closure A))) ⊆
          interior (closure (closure A)) :=
      interiorClosureInterior_subset_interiorClosure (A := closure A)
    simpa [closure_closure] using h
  ·
    have h :
        interior (closure A) ⊆
          interior (closure (interior (closure A))) :=
      Topology.interior_subset_interiorClosureInterior (A := closure A)
    simpa using h