

theorem interior_eq_self_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = A ↔ IsOpen A := by
  constructor
  · intro h_eq
    -- The interior of any set is open; rewrite using the hypothesis.
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro h_open
    -- For an open set, the interior is itself.
    simpa using h_open.interior_eq