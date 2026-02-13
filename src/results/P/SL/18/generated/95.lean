

theorem closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    closure (interior (closure (A : Set X))) = Set.univ := by
  have hInt : interior (closure (A : Set X)) = Set.univ :=
    Topology.interior_closure_eq_univ_of_dense (A := A) hDense
  calc
    closure (interior (closure (A : Set X)))
        = closure (Set.univ : Set X) := by
          simpa [hInt]
    _ = (Set.univ : Set X) := by
          simpa