

theorem closure_interior_inter_open_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (interior (A ∩ B : Set X)) = closure (A ∩ interior B) := by
  -- Use the general formula for the interior of an intersection.
  have hInt : interior (A ∩ B : Set X) = interior A ∩ interior B :=
    interior_inter
  -- Since `A` is open, its interior is itself.
  have hIntA : interior (A : Set X) = A := hA.interior_eq
  -- Rewrite the interior of the intersection accordingly.
  have hEq : interior (A ∩ B : Set X) = A ∩ interior B := by
    simpa [hIntA] using hInt
  -- Take closures of both sides of the equality.
  simpa [hEq]