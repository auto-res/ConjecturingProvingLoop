

theorem Topology.closure_interior_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxClInt, hxIntCompl⟩
    -- `closure (interior A)` sits inside `closure A`.
    have h_closure_mono :
        closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (X := X) (A := A)
    have hxClA : x ∈ closure A := h_closure_mono hxClInt
    -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
    have h_eq :
        interior (Aᶜ) = (closure A)ᶜ :=
      Topology.interior_compl_eq_compl_closure (X := X) (A := A)
    have hxNotClA : x ∈ (closure A)ᶜ := by
      simpa [h_eq] using hxIntCompl
    -- Contradiction.
    exact (hxNotClA hxClA).elim
  · exact Set.empty_subset _