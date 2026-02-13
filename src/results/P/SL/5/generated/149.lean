

theorem closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxCl, hxInt⟩
  -- We show `x ∈ closure (A ∩ B)` using the characterization via open neighborhoods.
  have : x ∈ closure (A ∩ B : Set X) := by
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighborhood `U ∩ interior B` of `x`.
    have hVopen : IsOpen (U ∩ interior B) := hUopen.inter isOpen_interior
    have hxV : x ∈ U ∩ interior B := ⟨hxU, hxInt⟩
    -- Since `x ∈ closure A`, this neighborhood meets `A`.
    have h_non : ((U ∩ interior B) ∩ (A : Set X)).Nonempty := by
      have hClosure := (mem_closure_iff).1 hxCl
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        using hClosure (U ∩ interior B) hVopen hxV
    -- Extract a witness in `U ∩ (A ∩ B)`.
    rcases h_non with ⟨y, hy⟩
    rcases hy with ⟨⟨hyU, hyIntB⟩, hyA⟩
    have hyB : y ∈ B := interior_subset hyIntB
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this