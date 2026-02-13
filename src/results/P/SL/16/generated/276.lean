

theorem Topology.interior_inter_closure_compl_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior A ∩ closure (Aᶜ) : Set X) = (∅ : Set X) := by
  -- We show that the intersection contains no points.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hx
  rcases hx with ⟨hxInt, hxClCompl⟩
  -- `interior A` is an open neighbourhood of `x` contained in `A`.
  have hOpen : IsOpen (interior A) := isOpen_interior
  -- Since `x ∈ closure (Aᶜ)`, every such neighbourhood meets `Aᶜ`.
  have hNonempty :=
    (mem_closure_iff.1 hxClCompl) (interior A) hOpen hxInt
  rcases hNonempty with ⟨y, ⟨hyInt, hyCompl⟩⟩
  -- But `interior A ⊆ A`, so `y ∈ A`, contradicting `y ∈ Aᶜ`.
  exact hyCompl (interior_subset hyInt)