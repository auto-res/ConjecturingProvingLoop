

theorem closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∩ interior (closure A) = interior (closure A) := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact And.intro
      ((interior_subset : interior (closure A) ⊆ closure A) hx)
      hx