

theorem Topology.interior_inter_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We verify the neighbourhood criterion for `x ∈ closure (A ∩ B)`.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- Consider the neighbourhood `U ∩ interior A`, which is open and contains `x`.
  have hWopen : IsOpen (U ∩ interior A) := hUopen.inter isOpen_interior
  have hxW   : x ∈ U ∩ interior A := ⟨hxU, hxIntA⟩
  -- Since `x ∈ closure B`, this neighbourhood meets `B`.
  have h_nonempty : ((U ∩ interior A) ∩ B).Nonempty :=
    (mem_closure_iff).1 hxClB (U ∩ interior A) hWopen hxW
  -- Extract a witness lying in `U ∩ (A ∩ B)`.
  rcases h_nonempty with ⟨y, ⟨⟨hyU, hyIntA⟩, hyB⟩⟩
  have hyA : y ∈ A := interior_subset hyIntA
  exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩