

theorem Topology.iterate_closure_interior_fixed_aux {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    ∀ n : ℕ,
      ((fun S : Set X => closure (interior S))^[n]) (closure (interior A)) =
        closure (interior A) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- `closure (interior A)` is a fixed point of the operator `S ↦ closure (interior S)`
      have h_fix :
          closure (interior (closure (interior A))) = closure (interior A) := by
        simpa using
          Topology.closure_interior_closure_interior_eq_closure_interior
            (X := X) (A := A)
      -- Use the fixed-point property to simplify the `(n + 1)`-st iterate.
      simp [Function.iterate_succ_apply', ih, h_fix]