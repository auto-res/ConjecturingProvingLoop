

theorem Topology.interior_diff_closure_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A \ closure A = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxInt, hxNotCl⟩
    have hxCl : x ∈ closure A := subset_closure (interior_subset hxInt)
    exact (hxNotCl hxCl).elim
  · intro hx
    cases hx