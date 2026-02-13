

theorem Topology.iterate_interior_closure_fixed_aux
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      interior (closure ((fun S : Set X => interior (closure S))^[n] A)) =
        interior (closure A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Function.iterate_succ_apply', ih,
        Topology.interior_closure_interior_closure_eq_interior_closure
          (X := X)
          (A := ((fun S : Set X => interior (closure S))^[n] A))]