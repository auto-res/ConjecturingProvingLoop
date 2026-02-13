

theorem interior_closure_union_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) (hDenseB : Dense (B : Set X)) :
    interior (closure (A ∪ B : Set X)) = (Set.univ : Set X) := by
  -- `Dense` sets have closures equal to `univ`.
  have hClosA : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDenseA
  have hClosB : closure (B : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := B)).1 hDenseB
  -- Compute the closure of the union.
  have hClosUnion : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    calc
      closure (A ∪ B : Set X)
          = closure (A : Set X) ∪ closure (B : Set X) := by
              simpa [closure_union]
      _ = (Set.univ : Set X) ∪ (Set.univ : Set X) := by
              simpa [hClosA, hClosB]
      _ = (Set.univ : Set X) := by
              simp
  -- The interior of `univ` is `univ`.
  simpa [hClosUnion, interior_univ]