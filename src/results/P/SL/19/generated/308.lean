

theorem Topology.open_inter_frontier_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    (A ∩ frontier A : Set X) = (∅ : Set X) := by
  -- First show that `A ∩ frontier A` is empty.
  have hSub : (A ∩ frontier A : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    rcases hx with ⟨hxA, hxFront⟩
    -- For an open set `A`, the frontier is contained in the complement of `A`.
    have hFrontSub : frontier A ⊆ Aᶜ :=
      Topology.frontier_subset_compl_of_isOpen (A := A) hA
    -- Hence `x ∈ Aᶜ`, contradicting `x ∈ A`.
    have : x ∈ Aᶜ := hFrontSub hxFront
    exact (this hxA).elim
  -- The reverse inclusion is trivial.
  have hEmptySub : (∅ : Set X) ⊆ (A ∩ frontier A : Set X) := by
    intro x hx
    cases hx
  -- Combine the two inclusions to get the desired equality of sets.
  exact Set.Subset.antisymm hSub hEmptySub