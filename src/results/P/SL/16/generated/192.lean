

theorem Topology.iterate_interior_closure_fixed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      ((fun S : Set X => interior (closure S))^[n]) (interior (closure A)) =
        interior (closure A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Function.iterate_succ_apply', ih,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X) (A := A)]