

theorem closureInterior_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxClIntA, hxIntB⟩
  -- We will show `x ∈ closure (A ∩ B)` using the neighbourhood criterion.
  have : x ∈ closure (A ∩ B : Set X) := by
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighbourhood `V = U ∩ interior B` of `x`.
    have hVopen : IsOpen (U ∩ interior B) := hUopen.inter isOpen_interior
    have hxV : x ∈ U ∩ interior B := ⟨hxU, hxIntB⟩
    -- Since `x ∈ closure (interior A)`, this neighbourhood meets `interior A`.
    have hNon : ((U ∩ interior B : Set X) ∩ interior A).Nonempty := by
      have h := (mem_closure_iff).1 hxClIntA
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        using h (U ∩ interior B) hVopen hxV
    -- Extract a point `y` in the intersection.
    rcases hNon with ⟨y, ⟨⟨hyU, hyIntB⟩, hyIntA⟩⟩
    have hyA : y ∈ A := interior_subset hyIntA
    have hyB : y ∈ B := interior_subset hyIntB
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this