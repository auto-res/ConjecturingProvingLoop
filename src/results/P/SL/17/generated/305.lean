

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hx_clA, hx_intB⟩
  -- We show `x ∈ closure (A ∩ B)` using the neighbourhood characterization.
  apply (mem_closure_iff).2
  intro U hU_open hxU
  -- Refine the neighbourhood to stay inside `B`.
  have hV_open : IsOpen (U ∩ interior B) := hU_open.inter isOpen_interior
  have hxV : x ∈ U ∩ interior B := ⟨hxU, hx_intB⟩
  -- Since `x ∈ closure A`, this refined neighbourhood meets `A`.
  have h_nonempty : ((U ∩ interior B) ∩ A).Nonempty := by
    have := (mem_closure_iff).1 hx_clA (U ∩ interior B) hV_open hxV
    simpa [Set.inter_left_comm, Set.inter_assoc] using this
  -- Extract a witness in the required intersection.
  rcases h_nonempty with ⟨y, ⟨⟨hyU, hyIntB⟩, hyA⟩⟩
  have hyB : y ∈ B := interior_subset hyIntB
  exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩