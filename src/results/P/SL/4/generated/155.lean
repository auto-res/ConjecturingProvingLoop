

theorem closure_interior_inter_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior A) ∩ closure A = closure (interior A) := by
  ext x
  constructor
  · intro h
    exact h.1
  · intro hx
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_interior_subset_closure (X := X) (A := A)
    exact And.intro hx (h_subset hx)