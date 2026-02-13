

theorem interior_inter_interior_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (interior A ∩ interior B) = interior A ∩ interior B := by
  -- `interior A` and `interior B` are open, hence so is their intersection.
  have hOpen : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  -- For an open set, the interior equals the set itself.
  simpa [hOpen.interior_eq]