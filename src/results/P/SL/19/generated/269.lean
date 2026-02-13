

theorem Topology.interior_inter_closure_subset_closure_inter {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior A ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClosB⟩
  -- Prove the membership in the closure via the neighbourhood characterization.
  have h : ∀ U, IsOpen U → x ∈ U → (U ∩ (A ∩ B)).Nonempty := by
    intro U hU hxU
    -- The open set `U ∩ interior A` still contains `x`.
    have hV_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
    have hxV : x ∈ U ∩ interior A := ⟨hxU, hxIntA⟩
    -- Since `x ∈ closure B`, this open set meets `B`.
    have hNon : ((U ∩ interior A) ∩ B).Nonempty :=
      (mem_closure_iff.1 hxClosB) (U ∩ interior A) hV_open hxV
    rcases hNon with ⟨y, ⟨⟨hyU, hyIntA⟩, hyB⟩⟩
    -- The point `y` lies in `A` because it lies in `interior A`.
    have hyA : y ∈ A := interior_subset hyIntA
    -- Hence `y ∈ U ∩ (A ∩ B)`.
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact (mem_closure_iff).2 h