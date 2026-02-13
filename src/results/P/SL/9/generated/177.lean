

theorem Topology.interior_inter_interiorCompl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We prove the intersection is empty by showing no element belongs to it.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hx_intA, hx_intAc⟩
  -- From membership in the interiors, deduce membership in the underlying sets.
  have hA  : x ∈ A   := interior_subset hx_intA
  have hAc : x ∈ Aᶜ := interior_subset hx_intAc
  -- The two memberships are incompatible.
  exact hAc hA