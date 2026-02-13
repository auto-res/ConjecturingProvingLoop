

theorem interior_inter_eq_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = interior A ∩ interior B := by
  -- `A ∩ B` is open because it is the intersection of two open sets.
  have hOpen : IsOpen ((A ∩ B) : Set X) := hA.inter hB
  -- The interior of an open set is the set itself.
  simpa [hA.interior_eq, hB.interior_eq, hOpen.interior_eq]