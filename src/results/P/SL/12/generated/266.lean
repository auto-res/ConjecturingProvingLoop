

theorem Topology.interior_inter_closure_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ∩ closure (Aᶜ : Set X) = (∅ : Set X) := by
  simpa [compl_compl] using
    (Topology.interior_compl_inter_closure_eq_empty (X := X) (A := Aᶜ))