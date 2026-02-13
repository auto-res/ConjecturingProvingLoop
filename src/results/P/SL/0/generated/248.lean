

theorem union_interiors_eq_interior_union_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A : Set X) ∪ interior (B : Set X) = interior (A ∪ B : Set X) := by
  calc
    interior (A : Set X) ∪ interior (B : Set X)
        = (A : Set X) ∪ (B : Set X) := by
          simp [hA.interior_eq, hB.interior_eq]
    _ = interior (A ∪ B : Set X) := by
          have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
          simpa [hOpen.interior_eq]