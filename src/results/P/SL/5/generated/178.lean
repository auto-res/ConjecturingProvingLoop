

theorem interior_closure_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro x hx
  -- Rewrite the membership using the equality provided by `P2`.
  have hEq := Topology.interior_closure_eq_of_P2 (X := X) (A := A) h
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [hEq] using hx
  -- Use `interior_subset` to step from the interior to the closure.
  exact interior_subset hx'