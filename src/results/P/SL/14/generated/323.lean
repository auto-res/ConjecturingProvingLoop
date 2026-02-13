

theorem Topology.closureInterior_inter_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A ∩ closure (A : Set X))) = closure (interior A) := by
  have h : (A ∩ closure (A : Set X) : Set X) = A := by
    simpa using
      (Set.inter_eq_left.2 (subset_closure : (A : Set X) ⊆ closure A))
  simpa [h]