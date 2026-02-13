

theorem Topology.iterate_closure_interior_fixed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    ∀ n : ℕ,
      ((fun S : Set X => closure (interior S))^[n]) (closure (interior A)) =
        closure (interior A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Function.iterate_succ_apply', ih,
        Topology.closure_interior_closure_interior_eq_closure_interior
          (X := X) (A := closure (interior A))]