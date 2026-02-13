

theorem closure_interior_inter_right_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (interior A ∩ B) := by
  have hInt : interior (A ∩ B) = interior A ∩ B :=
    interior_inter_right_open (A := A) (B := B) hB
  simpa [hInt]