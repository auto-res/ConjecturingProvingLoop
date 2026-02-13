

theorem interior_closure_iterate_fixed {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure S)) n (interior (closure A)) =
      interior (closure A) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Nat.iterate, ih,
        Topology.interior_closure_idempotent (X := X) (A := A)]