

theorem Topology.interior_diff_eq_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) = interior A \ closure B := by
  apply Set.Subset.antisymm
  ·
    -- One inclusion is already available.
    exact
      Topology.interior_diff_subset_interior_diff (A := A) (B := B)
  ·
    -- Prove the reverse inclusion.
    intro x hx
    rcases hx with ⟨hxIntA, hxNotClB⟩
    -- Consider the open set `interior A ∩ (closure B)ᶜ` containing `x`.
    have h_open : IsOpen (interior A ∩ (closure B)ᶜ) :=
      isOpen_interior.inter isClosed_closure.isOpen_compl
    have hx_mem : x ∈ interior A ∩ (closure B)ᶜ :=
      And.intro hxIntA hxNotClB
    -- This open set is contained in `A \ B`.
    have h_subset : (interior A ∩ (closure B)ᶜ) ⊆ (A \ B) := by
      intro y hy
      rcases hy with ⟨hyIntA, hyNotClB⟩
      have hyA : y ∈ A := interior_subset hyIntA
      have hyNotB : y ∉ B := by
        intro hyB
        have : y ∈ closure B := subset_closure hyB
        exact hyNotClB this
      exact And.intro hyA hyNotB
    -- Hence, the open set is contained in the interior of `A \ B`.
    have h_interior :
        interior A ∩ (closure B)ᶜ ⊆ interior (A \ B) :=
      interior_maximal h_subset h_open
    -- Conclude that `x` is in the interior of `A \ B`.
    exact h_interior hx_mem