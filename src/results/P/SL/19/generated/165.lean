

theorem Topology.closure_diff_interior_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A \ interior A) ∩ interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxClos, hxInt⟩
    -- Using the characterization of the closure with an open neighbourhood.
    have hNon :
        ((interior A) ∩ (A \ interior A)).Nonempty :=
      (mem_closure_iff).1 hxClos (interior A) isOpen_interior hxInt
    rcases hNon with ⟨y, ⟨hyInt, hyDiff⟩⟩
    -- `hyDiff` yields `y ∉ interior A`, contradicting `hyInt`.
    exact False.elim (hyDiff.2 hyInt)
  · exact Set.empty_subset _