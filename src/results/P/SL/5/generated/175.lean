

theorem closure_inter_interior_subset_closure_inter' {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxIntB⟩
  -- We will show `x ∈ closure (A ∩ B)` via the neighbourhood
  -- characterisation of the closure.
  have : x ∈ closure (A ∩ B : Set X) := by
    -- Reformulate membership in the closure.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighbourhood `U ∩ interior B` of `x`.
    have hVopen : IsOpen (U ∩ interior B) := hUopen.inter isOpen_interior
    have hxV : x ∈ U ∩ interior B := ⟨hxU, hxIntB⟩
    -- As `x ∈ closure A`, this neighbourhood meets `A`.
    have hNon : ((U ∩ interior B) ∩ (A : Set X)).Nonempty := by
      have h := (mem_closure_iff).1 hxClA
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        using h (U ∩ interior B) hVopen hxV
    -- Extract a witness `y` in the intersection.
    rcases hNon with ⟨y, ⟨⟨hyU, hyIntB⟩, hyA⟩⟩
    -- `y` also lies in `B` since it is in `interior B`.
    have hyB : y ∈ B := interior_subset hyIntB
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this