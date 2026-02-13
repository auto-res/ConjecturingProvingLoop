

theorem Topology.closure_interior_compl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (Aᶜ)) ∩ interior A = (∅ : Set X) := by
  simpa [Set.compl_compl] using
    (Topology.closure_interior_inter_interior_compl_eq_empty
      (X := X) (A := Aᶜ))