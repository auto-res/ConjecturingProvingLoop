

theorem interior_closure_inter_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∩ closure A = interior (closure A) := by
  ext x
  constructor
  · intro h
    exact h.1
  · intro hx
    exact And.intro hx (interior_subset hx)