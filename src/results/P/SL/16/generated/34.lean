

theorem Topology.closed_P2_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) :
    closure (interior A) = A := by
  -- From `P2` and closedness we know `A` is open
  have hOpen : IsOpen A := Topology.closed_P2_isOpen (X := X) (A := A) hClosed hP2
  -- Hence `interior A = A`
  have hInt : interior A = A := hOpen.interior_eq
  -- And `closure A = A`
  have hCl : closure A = A := hClosed.closure_eq
  -- Putting these equalities together
  calc
    closure (interior A) = closure A := by
      simpa [hInt]
    _ = A := by
      simpa [hCl]