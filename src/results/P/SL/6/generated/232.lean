

theorem closure_interior_inter_eq_closure_inter_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior ((A ∩ B) : Set X)) = closure (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  -- For an open set, its interior equals the set itself.
  have hInt : interior ((A ∩ B) : Set X) = A ∩ B := hOpen.interior_eq
  simpa [hInt]