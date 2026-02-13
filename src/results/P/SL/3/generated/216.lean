

theorem P3_union_dense {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : closure (A : Set X) = (Set.univ : Set X))
    (hB : closure (B : Set X) = (Set.univ : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- First, observe that `A ∪ B` is dense.
  have hDenseUnion : closure ((A ∪ B) : Set X) = (Set.univ : Set X) := by
    have h := closure_union_eq_union_closure (A := A) (B := B)
    simpa [hA, hB, Set.union_univ, Set.univ_union] using h
  -- A dense set satisfies `P3`.
  exact Topology.P3_of_dense (A := A ∪ B) hDenseUnion