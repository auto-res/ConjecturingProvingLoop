

theorem Topology.interior_diff_closed_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hOpenA : IsOpen A) (hClosedB : IsClosed B) :
    interior (A \ B) = A \ B := by
  simpa [hOpenA.interior_eq] using
    (Topology.interior_diff_closed (A := A) (B := B) hClosedB)