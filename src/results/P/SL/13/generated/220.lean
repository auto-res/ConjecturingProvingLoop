

theorem Topology.closure_eq_univ_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = (Set.univ : Set X)) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  -- `x` is certainly in the closure of `A`.
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  -- Rewrite using the hypothesis `h` and simplify.
  simpa [h, interior_univ] using hx_cl