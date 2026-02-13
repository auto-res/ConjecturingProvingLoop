

theorem Topology.inter_interiorCompl_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X) ∩ interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We prove the intersection is empty by showing no element belongs to it.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hxA, hxIntCompl⟩
  have hxAc : x ∈ (Aᶜ : Set X) := interior_subset hxIntCompl
  exact hxAc hxA