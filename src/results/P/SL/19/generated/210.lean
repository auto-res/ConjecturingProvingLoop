

theorem Topology.frontier_interior_eq_closure_interior_inter_frontier {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier (interior A) = closure (interior A) ∩ frontier A := by
  have h₁ :=
    Topology.frontier_interior_eq_closure_interior_diff_interior
      (X := X) (A := A)
  have h₂ :=
    Topology.closure_interior_inter_frontier_eq_closure_interior_diff_interior
      (X := X) (A := A)
  calc
    frontier (interior A)
        = closure (interior A) \ interior A := by
          simpa using h₁
    _ = closure (interior A) ∩ frontier A := by
          simpa using (h₂.symm)