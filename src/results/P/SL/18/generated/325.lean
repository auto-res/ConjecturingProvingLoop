

theorem interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen (U : Set X)) :
    interior (U ∩ A : Set X) = U ∩ interior A := by
  simpa [hU.interior_eq] using
    (interior_inter (A := U) (B := A))