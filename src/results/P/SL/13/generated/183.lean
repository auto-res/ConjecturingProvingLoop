

theorem Topology.closure_inter_interior_subset_closure_inter {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hx_clA, hx_intB⟩
  -- We prove that `x` belongs to the closure of `A ∩ B`.
  have : (x : X) ∈ closure (A ∩ B) := by
    -- Neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro U hU_open hxU
    -- Consider the open neighbourhood `U ∩ interior B` of `x`.
    have hV_open : IsOpen (U ∩ interior B) := hU_open.inter isOpen_interior
    have hxV : (x : X) ∈ U ∩ interior B := ⟨hxU, hx_intB⟩
    -- Since `x ∈ closure A`, this set meets `A`.
    have h_nonempty :
        ((U ∩ interior B) ∩ A : Set X).Nonempty := by
      have h_prop := (mem_closure_iff).1 hx_clA
      have h := h_prop (U ∩ interior B) hV_open hxV
      simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using h
    -- Extract a witness in `U ∩ (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyU, hy_intB⟩, hyA⟩⟩
    have hyB : (y : X) ∈ B := interior_subset hy_intB
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this