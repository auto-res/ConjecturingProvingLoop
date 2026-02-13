

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  -- First, translate `P2` into openness for a closed set.
  have hP2_open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_open (A := A) hA_closed
  -- Next, characterize openness via the interior.
  have hOpen_int : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  exact hP2_open.trans hOpen_int