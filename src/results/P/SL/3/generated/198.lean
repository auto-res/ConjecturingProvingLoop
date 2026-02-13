

theorem interior_inter_closure_diff_interior_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) ∩ (closure (A : Set X) \ interior (A : Set X)) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxInt, ⟨_, hxNotInt⟩⟩
    exact (hxNotInt hxInt).elim
  · exact Set.empty_subset _