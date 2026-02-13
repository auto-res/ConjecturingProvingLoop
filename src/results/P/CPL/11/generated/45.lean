

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : P1 (closure (interior A)) := by
  -- `P1` holds for `interior A`.
  have h_int : P1 (interior A) := P1_interior (A := A)
  -- Hence it also holds for the closure of `interior A`.
  simpa using (P1_closure (A := interior A) h_int)