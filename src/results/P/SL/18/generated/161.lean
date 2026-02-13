

theorem closure_interior_eq_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure (interior A) = closure (interior (closure A)) := by
  apply Set.Subset.antisymm
  ·
    exact
      Topology.closure_interior_subset_closure_interior_closure (A := A)
  ·
    have hInt :
        interior (closure A) = interior (closure (interior A)) :=
      Topology.interior_closure_eq_interior_closure_interior_of_P1
        (A := A) hP1
    have hEq :
        closure (interior (closure A)) = closure (interior A) := by
      calc
        closure (interior (closure A))
            = closure (interior (closure (interior A))) := by
              simpa [hInt]
        _ = closure (interior A) := by
              simpa using
                (Topology.closure_interior_closure_interior_eq_closure_interior
                  (A := A))
    simpa [hEq] using (Set.Subset.rfl)