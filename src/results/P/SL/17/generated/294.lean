

theorem Topology.interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure A) ⊆ closure (interior A) := by
  intro x hx
  -- First, note that `x ∈ closure A` because `interior (closure A) ⊆ closure A`.
  have hx_closureA : x ∈ closure A := interior_subset hx
  -- Under `P1`, the two closures coincide.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
  -- Rewrite to obtain the desired membership.
  simpa [h_eq] using hx_closureA