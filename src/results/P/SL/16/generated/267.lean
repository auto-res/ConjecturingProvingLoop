

theorem Topology.P1_iterate_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      Topology.P1 (X := X)
        (((fun S : Set X => interior (closure S))^[n.succ]) A) := by
  intro n
  -- Define the operator `f : Set X → Set X`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- The `(n.succ)`-th iterate of `f` applied to `A` is the open set
  -- `interior (closure ((f^[n]) A))`.
  have hOpen : IsOpen (interior (closure ((f^[n]) A))) := isOpen_interior
  -- Any open set satisfies `P1`.
  have hP1 : Topology.P1 (X := X) (interior (closure ((f^[n]) A))) :=
    Topology.isOpen_implies_P1
      (X := X) (A := interior (closure ((f^[n]) A))) hOpen
  -- Rewrite to match the desired form.
  simpa [f, Function.iterate_succ_apply'] using hP1