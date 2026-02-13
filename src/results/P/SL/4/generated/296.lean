

theorem frontier_subset_closure_diff_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    frontier (A : Set X) ⊆ closure A \ interior A := by
  intro x hx
  have hx_cl : x ∈ closure A :=
    frontier_subset_closure (X := X) (A := A) hx
  have hx_not_int : x ∉ interior A :=
    (frontier_subset_compl_interior (X := X) (A := A)) hx
  exact And.intro hx_cl hx_not_int