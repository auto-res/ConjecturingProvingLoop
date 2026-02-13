

theorem closure_eq_union_boundary_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    closure (A : Set X) = (A : Set X) ∪ (closure (A : Set X) \ A) := by
  simpa [hA.interior_eq] using
    (closure_eq_interior_union_closure_diff_interior (A := A))