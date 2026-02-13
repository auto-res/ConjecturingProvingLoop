

theorem closure_interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen (B : Set X)) :
    closure (interior (A ∩ B : Set X)) = closure (interior A ∩ B) := by
  -- Use the general formula for the interior of an intersection.
  have hInt : interior (A ∩ B : Set X) = interior A ∩ interior B :=
    interior_inter
  -- Since `B` is open, its interior coincides with itself.
  have hIntB : interior (B : Set X) = B := hB.interior_eq
  -- Rewrite the interior of the intersection accordingly.
  have hEq : interior (A ∩ B : Set X) = interior A ∩ B := by
    simpa [hIntB] using hInt
  -- Take closures on both sides of the equality.
  simpa [hEq]