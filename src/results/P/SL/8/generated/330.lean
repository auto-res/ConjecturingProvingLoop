

theorem interior_diff_closed_eq_self {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsClosed B) :
    interior (A \ B) = A \ B := by
  have h := interior_diff_eq_self_diff_closure (X := X) (A := A) (B := B) hA
  simpa [hB.closure_eq] using h