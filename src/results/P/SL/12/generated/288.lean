

theorem Topology.interior_compl_eq_empty_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : closure (A : Set X) = (Set.univ : Set X)) :
    interior (Aᶜ : Set X) = (∅ : Set X) := by
  -- We first show that `interior (Aᶜ)` is contained in `∅`.
  have h_subset : (interior (Aᶜ : Set X)) ⊆ (∅ : Set X) := by
    intro x hx_int
    -- We will derive a contradiction from the assumption that
    -- `x ∈ interior (Aᶜ)`.
    have hx_closure : (x : X) ∈ closure (A : Set X) := by
      -- Since `closure A = univ`, every point lies in `closure A`.
      simpa [hA] using (by
        have : (x : X) ∈ (Set.univ : Set X) := by simp
        exact this)
    -- Use the neighbourhood characterisation of the closure with the open set
    -- `interior (Aᶜ)`, which contains `x`.
    have h_nonempty :
        ((interior (Aᶜ : Set X)) ∩ A).Nonempty :=
      (mem_closure_iff).1 hx_closure (interior (Aᶜ : Set X))
        isOpen_interior hx_int
    rcases h_nonempty with ⟨y, ⟨hy_int, hyA⟩⟩
    -- But `y ∈ interior (Aᶜ)` implies `y ∉ A`, contradicting `hyA`.
    have : (y : X) ∈ (Aᶜ : Set X) := interior_subset hy_int
    exact (this hyA).elim
  -- The reverse inclusion `∅ ⊆ interior (Aᶜ)` is trivial.
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)