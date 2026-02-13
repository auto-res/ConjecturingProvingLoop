

theorem Topology.isClopen_iff_closed_and_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A ↔ IsClosed A ∧ interior A = (A : Set X) := by
  constructor
  · intro h
    have hClosed : IsClosed A := h.1
    have hOpen : IsOpen A := h.2
    have hInt : interior A = (A : Set X) := hOpen.interior_eq
    exact And.intro hClosed hInt
  · rintro ⟨hClosed, hInt⟩
    have hOpen : IsOpen A := by
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hInt] using hOpenInt
    exact And.intro hClosed hOpen