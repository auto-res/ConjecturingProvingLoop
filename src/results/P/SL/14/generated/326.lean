

theorem Topology.interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We prove `x ∈ closure (A ∩ B)` using the neighbourhood characterization.
  have : (x : X) ∈ closure (A ∩ B) := by
    refine (mem_closure_iff).2 ?_
    intro U hU hxU
    -- Consider the open set `U ∩ interior A`, an open neighbourhood of `x`
    -- contained in `A`.
    have hV_open : IsOpen (U ∩ interior (A : Set X)) :=
      IsOpen.inter hU isOpen_interior
    have hxV : (x : X) ∈ U ∩ interior (A : Set X) := ⟨hxU, hxIntA⟩
    -- Since `x ∈ closure B`, this neighbourhood meets `B`.
    have hNonempty :
        ((U ∩ interior (A : Set X)) ∩ (B : Set X)).Nonempty :=
      (mem_closure_iff).1 hxClB (U ∩ interior A) hV_open hxV
    -- Extract a witness `y ∈ U ∩ (A ∩ B)`.
    rcases hNonempty with ⟨y, ⟨hyU, hyIntA⟩, hyB⟩
    have hyA : (y : X) ∈ A := interior_subset hyIntA
    exact ⟨y, hyU, ⟨hyA, hyB⟩⟩
  exact this