

theorem dense_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P2 (closure A) := by
  -- The set `closure A` is `univ`, hence open.
  have hOpen : IsOpen (closure A) := by
    simpa [h_dense] using isOpen_univ
  -- Openness of `closure A` immediately yields `P2`.
  exact isOpen_closure_imp_P2_closure (X := X) (A := A) hOpen