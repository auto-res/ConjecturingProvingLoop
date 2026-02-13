

theorem interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : interior (closure A) = interior (closure (interior A)) := by
  have hcl : closure (A : Set X) = closure (interior A) :=
    closure_eq_of_P2 (A := A) h
  simpa [hcl]