

theorem Topology.P3_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔ interior (A : Set X) = A := by
  -- First, recall that for a closed set `A`, `P3 A` is equivalent to `A` being open.
  have h1 : Topology.P3 (X := X) A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) h_closed
  -- For any set, being open is equivalent to coinciding with its interior.
  have h2 : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro h_open
      simpa using h_open.interior_eq
    · intro h_int_eq
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [h_int_eq] using this
  -- Combine the two equivalences.
  exact h1.trans h2