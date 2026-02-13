

theorem Topology.interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∩ closure (B : Set X) ⊆ closure (A ∩ B : Set X) := by
  intro x hx
  rcases hx with ⟨hx_intA, hx_clB⟩
  -- We prove that every open neighbourhood of `x` intersects `A ∩ B`.
  have : x ∈ closure (A ∩ B : Set X) := by
    apply (mem_closure_iff).2
    intro V hV_open hxV
    -- Consider the open neighbourhood `V ∩ interior A` of `x`.
    have hU_open : IsOpen (V ∩ interior (A : Set X)) :=
      hV_open.inter isOpen_interior
    have hxU : x ∈ V ∩ interior (A : Set X) := ⟨hxV, hx_intA⟩
    -- Since `x ∈ closure B`, this neighbourhood meets `B`.
    have h_nonempty :
        ((V ∩ interior (A : Set X)) ∩ B).Nonempty :=
      (mem_closure_iff).1 hx_clB (V ∩ interior (A : Set X)) hU_open hxU
    -- Extract a witness and show it lies in `V ∩ (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyV, hy_intA⟩, hyB⟩⟩
    have hyA : y ∈ A := interior_subset hy_intA
    exact ⟨y, ⟨hyV, ⟨hyA, hyB⟩⟩⟩
  exact this