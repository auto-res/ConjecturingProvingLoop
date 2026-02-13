

theorem P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  -- For closed sets, `P3` is equivalent to being open.
  have h₁ : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  -- A set is open iff its interior equals itself.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa [hOpen.interior_eq]
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  simpa using h₁.trans h₂