

theorem Topology.closure_interior_inter_eq_closure_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- Since `A` and `B` are open, so is `A ∩ B`, and its interior is itself.
  have hInt : interior (A ∩ B) = A ∩ B := (hA.inter hB).interior_eq
  -- Rewriting with `hInt` yields the desired equality.
  simpa [hInt]