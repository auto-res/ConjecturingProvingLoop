

theorem interior_closure_congr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : closure (A : Set X) = closure B) :
    interior (closure (A : Set X)) = interior (closure B) := by
  simpa [h] using
    (rfl : interior (closure (A : Set X)) = interior (closure (A : Set X)))