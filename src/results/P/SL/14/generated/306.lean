

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hx_clA, hx_intB⟩
  -- We prove `x ∈ closure (A ∩ B)` using the neighborhood characterization.
  have : (x : X) ∈ closure (A ∩ B) := by
    refine (mem_closure_iff).2 ?_
    intro U hU hxU
    -- The open set `U ∩ interior B` is an open neighbourhood of `x`.
    have hU' : IsOpen (U ∩ interior B) := IsOpen.inter hU isOpen_interior
    have hxU' : (x : X) ∈ U ∩ interior B := ⟨hxU, hx_intB⟩
    -- Since `x ∈ closure A`, this neighbourhood meets `A`.
    have hNonempty : ((U ∩ interior B) ∩ A).Nonempty :=
      (mem_closure_iff).1 hx_clA (U ∩ interior B) hU' hxU'
    rcases hNonempty with ⟨y, ⟨hyU, hy_intB⟩, hyA⟩
    -- The point `y` lies in `B` because it lies in `interior B`.
    have hyB : (y : X) ∈ B := interior_subset hy_intB
    exact ⟨y, hyU, ⟨hyA, hyB⟩⟩
  exact this