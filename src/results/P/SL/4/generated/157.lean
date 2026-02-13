

theorem interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ closure A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    have hxCl : x ∈ closure A := subset_closure hxA
    exact And.intro hxInt hxCl