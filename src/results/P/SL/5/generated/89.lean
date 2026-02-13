

theorem closure_interior_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    closure (interior A) = closure (interior (closure A)) := by
  apply le_antisymm
  ·
    exact
      Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A)
  ·
    intro x hx
    -- First, `x` lies in `closure A`.
    have hx_closureA :
        x ∈ closure (A : Set X) := by
      have hsubset :
          closure (interior (closure (A : Set X))) ⊆ closure A :=
        Topology.closure_interior_closure_subset_closure (X := X) (A := A)
      exact hsubset hx
    -- Use the equality `closure A = closure (interior A)` that follows from `P2`.
    have h_cl_eq :
        closure (A : Set X) = closure (interior A) :=
      Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hA
    simpa [h_cl_eq] using hx_closureA