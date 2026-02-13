

theorem interior_closure_inter_closure_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure A ∩ closure B) = interior A ∩ interior B := by
  -- Since `A` and `B` are closed, their closures are the sets themselves.
  have hA_cl : closure A = (A : Set X) := hA.closure_eq
  have hB_cl : closure B = (B : Set X) := hB.closure_eq
  -- Rewrite and apply the existing equality for closed intersections.
  simpa [hA_cl, hB_cl] using
    (interior_inter_eq_of_closed (A := A) (B := B) hA hB)