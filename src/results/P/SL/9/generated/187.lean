

theorem Topology.interior_inter_closureCompl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ∩ closure (Aᶜ) = (∅ : Set X) := by
  simpa [Set.inter_comm] using
    (Topology.closureCompl_inter_interior_eq_empty (A := A))