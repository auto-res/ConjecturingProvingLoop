

theorem Topology.interior_compl_inter_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ : Set X) ∩ closure (A : Set X) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hx_int, hx_cl⟩
    -- Use the neighbourhood formulation of `closure` with the open set
    -- `interior (Aᶜ)`, which contains `x`.
    have h_false : False := by
      rcases (mem_closure_iff).1 hx_cl
          (interior (Aᶜ : Set X)) isOpen_interior hx_int with
        ⟨y, hy_int, hyA⟩
      -- But `y ∈ interior (Aᶜ)` implies `y ∉ A`, contradicting `hyA`.
      have : y ∈ (Aᶜ : Set X) := interior_subset hy_int
      exact this hyA
    exact False.elim h_false
  · intro x hx
    cases hx