

theorem P2_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P2 (closure (A : Set X)) := by
  intro hDense
  -- `closure A` equals `univ` because `A` is dense.
  have hClosEq : closure (A : Set X) = Set.univ :=
    (Topology.dense_iff_closure_eq_univ).1 hDense
  -- Hence `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    simpa [hClosEq] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Apply the equivalence `P2 (closure A) ↔ IsOpen (closure A)`.
  have hEquiv :
      Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P2_closure_iff_open_closure (A := A)
  exact (hEquiv.mpr hOpen)