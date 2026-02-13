

theorem Topology.boundary_subset_closure_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ interior A ⊆ closure (Aᶜ) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotIntA⟩
  -- We verify the neighbourhood criterion for `x ∈ closure (Aᶜ)`.
  apply (mem_closure_iff).2
  intro V hVopen hxV
  -- Assume, for contradiction, that `V ∩ Aᶜ` is empty.
  by_contra hEmpty
  -- Then every point of `V` lies in `A`.
  have hSub : V ⊆ A := by
    intro y hyV
    by_contra hyNotA
    have : (V ∩ Aᶜ).Nonempty := ⟨y, ⟨hyV, hyNotA⟩⟩
    exact hEmpty this
  -- Hence `V` is an open neighbourhood of `x` contained in `A`,
  -- so `x ∈ interior A`, contradicting `hxNotIntA`.
  have : x ∈ interior A :=
    interior_maximal hSub hVopen hxV
  exact hxNotIntA this