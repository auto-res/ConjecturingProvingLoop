

theorem Topology.interior_closure_interior_inter_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B : Set X))) =
      interior (closure (interior A ∩ interior B)) := by
  have h : interior (A ∩ B : Set X) = interior A ∩ interior B := by
    simpa using Topology.interior_inter_eq (X := X) (A := A) (B := B)
  simpa [h]