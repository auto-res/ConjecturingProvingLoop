

theorem Topology.interior_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  have hA : (x : X) ∈ A := interior_subset hx.1
  have hAc : (x : X) ∈ Aᶜ := interior_subset hx.2
  exact hAc hA