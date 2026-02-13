

theorem interior_union_of_interiors {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((interior A) ∪ (interior B)) = (interior A) ∪ (interior B) := by
  -- The union of two open sets is open.
  have hOpen : IsOpen ((interior A) ∪ (interior B)) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  -- For open sets, the interior equals the set itself.
  simpa [hOpen.interior_eq]