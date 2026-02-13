

theorem closure_diff_subset_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A \ A ⊆ frontier A := by
  rintro x ⟨hx_cl, hx_notA⟩
  have hx_notInt : x ∉ interior A := by
    intro hx_int
    exact hx_notA (interior_subset hx_int)
  exact And.intro hx_cl hx_notInt