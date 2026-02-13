

theorem Topology.interior_inter_interiors_eq
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (interior A ∩ interior B) = interior A ∩ interior B := by
  -- `interior A` and `interior B` are open sets.
  have hA : IsOpen (interior A) := isOpen_interior
  have hB : IsOpen (interior B) := isOpen_interior
  -- Apply the general lemma for the interior of an intersection of open sets.
  simpa using (interior_inter hA hB)