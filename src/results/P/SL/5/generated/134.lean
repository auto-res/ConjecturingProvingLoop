

theorem interior_nonempty_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) (hA : A.Nonempty) :
    (interior (A : Set X)).Nonempty := by
  -- From closedness and `P3`, we know that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  -- For an open set, its interior is itself.
  have hInt_eq : interior (A : Set X) = A := hOpen.interior_eq
  -- The non‐emptiness of `A` now yields the non‐emptiness of its interior.
  simpa [hInt_eq] using hA