

theorem Topology.closure_interior_inter_eq_closure_inter_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- For open sets, taking the interior leaves the set unchanged.
  have hInt : interior (A ∩ B) = A ∩ B :=
    (Topology.interior_inter_eq_of_open (X := X) (A := A) (B := B) hA hB)
  simpa [hInt]