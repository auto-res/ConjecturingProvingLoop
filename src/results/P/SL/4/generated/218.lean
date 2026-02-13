

theorem closure_interior_inter_eq_closure_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- `A` and `B` are open, hence so is their intersection.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- For an open set, the interior equals the set itself.
  have hInt : interior (A ∩ B) = A ∩ B := hOpen.interior_eq
  -- Substitute this identity into the goal.
  simpa [hInt]