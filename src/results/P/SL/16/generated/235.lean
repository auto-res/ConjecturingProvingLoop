

theorem Topology.P2_iterate_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      Topology.P2 (X := X)
        (((fun S : Set X => interior (closure S))^[n.succ]) A) := by
  intro n
  -- Define the iteration function for clarity.
  let f : Set X → Set X := fun S => interior (closure S)
  -- Apply the lemma `P2_interior_closure` to the `n`-th iterate.
  have hP2 :
      Topology.P2 (X := X) (interior (closure ((f^[n]) A))) :=
    Topology.P2_interior_closure (X := X) (A := (f^[n]) A)
  -- Rewrite using the definition of the `(n.succ)`-th iterate.
  simpa [f, Function.iterate_succ_apply'] using hP2