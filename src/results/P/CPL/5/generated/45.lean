

theorem P1_diff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : IsClosed B) : P1 (A \ B) := by
  classical
  intro x hx
  -- `x` is in `A`, hence in the closure of `interior A` by `hA`.
  have hx_cl : x ∈ closure (interior A) := hA hx.1
  -- We prove that `x` is in the closure of `interior (A \ B)`.
  have : x ∈ closure (interior (A \ B)) := by
    -- Neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro V hVopen hxV
    -- Refine the neighbourhood to avoid `B`.
    have hWopen : IsOpen (V ∩ Bᶜ) := hVopen.inter hB.isOpen_compl
    have hxW : x ∈ V ∩ Bᶜ := by
      exact ⟨hxV, hx.2⟩
    -- This refined neighbourhood meets `interior A`.
    have h_non : ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
      have := (mem_closure_iff).1 hx_cl (V ∩ Bᶜ) hWopen hxW
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
    rcases h_non with ⟨y, hyW, hyIntA⟩
    -- `y` will be shown to lie in `interior (A \ B)`.
    have hyInt : y ∈ interior (A \ B) := by
      -- Consider the open set `U = interior A ∩ Bᶜ`.
      have hUopen : IsOpen (interior A ∩ Bᶜ) :=
        isOpen_interior.inter hB.isOpen_compl
      have hU_subset : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz
        exact ⟨(interior_subset : interior A ⊆ A) hz.1, hz.2⟩
      have hyU : y ∈ interior A ∩ Bᶜ := by
        have hyNotB : y ∈ Bᶜ := hyW.2
        exact ⟨hyIntA, hyNotB⟩
      exact
        mem_interior.2 ⟨interior A ∩ Bᶜ, hU_subset, hUopen, hyU⟩
    -- Provide the required witness in `V ∩ interior (A \ B)`.
    have hyV : y ∈ V := hyW.1
    exact ⟨y, hyV, hyInt⟩
  exact this