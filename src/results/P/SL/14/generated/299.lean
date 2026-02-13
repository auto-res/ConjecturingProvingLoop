

theorem Topology.interior_diff_interior_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A \ interior A : Set X) = (∅ : Set X) := by
  -- `interior (A \ interior A)` is an open subset of `A`
  have h_subset_int :
      (interior (A \ interior A : Set X) : Set X) ⊆ interior A := by
    -- First, note it lies in `A`
    have h_sub_A :
        (interior (A \ interior A : Set X) : Set X) ⊆ A := by
      intro x hx
      have hx_diff : (x : X) ∈ A \ interior A :=
        (interior_subset : interior (A \ interior A : Set X) ⊆ A \ interior A) hx
      exact hx_diff.1
    -- Then use maximality of the interior
    exact
      interior_maximal h_sub_A
        (isOpen_interior : IsOpen (interior (A \ interior A : Set X)))
  -- It is also disjoint from `interior A`
  have h_subset_compl :
      (interior (A \ interior A : Set X) : Set X) ⊆ (interior A)ᶜ := by
    intro x hx
    have hx_diff : (x : X) ∈ A \ interior A :=
      (interior_subset : interior (A \ interior A : Set X) ⊆ A \ interior A) hx
    exact hx_diff.2
  -- Hence it is contained in the empty set
  have h_subset_empty :
      (interior (A \ interior A : Set X) : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    have hx_in : (x : X) ∈ interior A := h_subset_int hx
    have hx_not : (x : X) ∉ interior A := h_subset_compl hx
    exact (hx_not hx_in).elim
  -- Equality with `∅`
  exact Set.Subset.antisymm h_subset_empty (Set.empty_subset _)