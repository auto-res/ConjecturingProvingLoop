

theorem Topology.P3_iterate_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    ∀ n : ℕ,
      Topology.P3 (X := X)
        (((fun S : Set X => interior (closure S))^[n.succ]) A) := by
  intro n
  -- Define the operator `f : Set X → Set X` as `S ↦ interior (closure S)`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- The `(n.succ)`-th iterate of `f` applied to `A` is an open set,
  -- namely `interior (closure ((f^[n]) A))`.
  have hOpen : IsOpen (interior (closure ((f^[n]) A))) := isOpen_interior
  -- Every open set satisfies `P3`.
  have hP3 : Topology.P3 (X := X) (interior (closure ((f^[n]) A))) :=
    Topology.isOpen_implies_P3
      (X := X) (A := interior (closure ((f^[n]) A))) hOpen
  -- Rewrite to match the desired form and conclude.
  simpa [f, Function.iterate_succ_apply'] using hP3