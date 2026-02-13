

theorem closure_inter_frontier_eq_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ frontier A = frontier A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hx_cl : x ∈ closure A :=
      (frontier_subset_closure (X := X) (A := A)) hx
    exact And.intro hx_cl hx