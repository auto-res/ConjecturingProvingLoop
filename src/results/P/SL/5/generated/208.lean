

theorem closure_interior_iterate_fixed {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior S)) n (closure (interior A)) =
      closure (interior A) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Nat.iterate, ih,
        Topology.closure_interior_idempotent (X := X) (A := interior A)]