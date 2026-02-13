

theorem isOpen_interior_closure_diff_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    IsOpen (interior (closure (A : Set X)) \ closure (interior A)) := by
  -- `interior (closure A)` is open, while `closure (interior A)` is closed,
  -- so their set‐difference is open.
  have h :
      IsOpen (interior (closure (A : Set X)) \ closure (interior A)) :=
    IsOpen.diff
      (X := X)
      (A := interior (closure (A : Set X)))
      (B := closure (interior A))
      isOpen_interior
      (isClosed_closure : IsClosed (closure (interior A)))
  simpa using h