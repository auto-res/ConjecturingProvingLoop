

theorem interior_inter_closure_subset_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We will show `x ∈ closure (A ∩ B)` using the neighbourhood
  -- characterization of the closure.
  have : x ∈ closure (A ∩ B : Set X) := by
    -- Apply `mem_closure_iff`.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Since `x ∈ interior A`, pick an open `V ⊆ A` with `x ∈ V`.
    rcases mem_interior.1 hxIntA with ⟨V, hVsubA, hVopen, hxV⟩
    -- Consider the open neighbourhood `W = U ∩ V` of `x`.
    have hWopen : IsOpen (U ∩ V) := hUopen.inter hVopen
    have hxW : x ∈ U ∩ V := ⟨hxU, hxV⟩
    -- Because `x ∈ closure B`, this neighbourhood meets `B`.
    have hNon : ((U ∩ V) ∩ (B : Set X)).Nonempty := by
      have hClosure := (mem_closure_iff).1 hxClB
      have : ((U ∩ V) ∩ B).Nonempty := hClosure (U ∩ V) hWopen hxW
      -- Rearrange intersections to match Lean's expectations.
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
    -- Extract a point `y` witnessing the non-emptiness.
    rcases hNon with ⟨y, ⟨⟨hyU, hyV⟩, hyB⟩⟩
    -- `y ∈ V ⊆ A`, hence `y ∈ A ∩ B` and `y ∈ U`.
    have hyA : y ∈ A := hVsubA hyV
    exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩
  exact this