

theorem Topology.P1_iterate_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    ∀ n : ℕ,
      Topology.P1 (X := X)
        (((fun S : Set X => closure (interior S))^[n.succ]) A) := by
  intro n
  induction n with
  | zero =>
      simpa using
        (Topology.P1_closure_interior (X := X) (A := A))
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using
        (Topology.P1_closure_interior (X := X)
          (A := ((fun S : Set X => closure (interior S))^[n.succ] A)))