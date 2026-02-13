

theorem Topology.P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact Topology.P1_implies_closure_interior_eq_closure (A := A) hP1
  · intro hEq
    -- we must show A ⊆ closure (interior A)
    intro x hxA
    have hx_closureA : x ∈ closure A := subset_closure hxA
    simpa [hEq] using hx_closureA