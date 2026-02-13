

theorem P3_union_left_dense {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) = (Set.univ : Set X) →
      Topology.P3 (A ∪ B) := by
  intro hDenseA
  -- First, show that the union has dense closure.
  have hCl : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    have hEq := closure_union_eq_union_closure (A := A) (B := B)
    simpa [hDenseA, Set.union_univ, Set.univ_union] using hEq
  -- Apply the existing lemma for dense sets.
  exact Topology.P3_of_dense (A := A ∪ B) hCl