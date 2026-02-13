

theorem Topology.closed_P3_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P3 (X := X) A ↔ interior A = A := by
  -- First, use the existing equivalence between `P3` and openness for closed sets.
  have h₀ := Topology.closed_P3_iff_isOpen (X := X) (A := A) hClosed
  -- We now relate openness to the interior being equal to the set itself.
  constructor
  · -- `P3 A → interior A = A`
    intro hP3
    -- Convert `P3` into openness via `h₀`.
    have hOpen : IsOpen A := (h₀).1 hP3
    -- For an open set, `interior` is itself.
    simpa using hOpen.interior_eq
  · -- `interior A = A → P3 A`
    intro hInt
    -- From the equality, deduce that `A` is open.
    have hOpen : IsOpen A := by
      -- `interior A` is open, and it equals `A`.
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hInt] using hOpenInt
    -- Convert openness back to `P3` via the established equivalence.
    exact (h₀).2 hOpen