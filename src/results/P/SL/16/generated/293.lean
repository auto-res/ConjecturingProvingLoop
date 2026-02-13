

theorem Topology.closure_interior_iterate_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      closure (interior (((fun S : Set X => closure (interior S))^[n]) A)) =
        closure (interior A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Function.iterate_succ_apply',
        Topology.closure_interior_closure_interior_eq_closure_interior, ih]