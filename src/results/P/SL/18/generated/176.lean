

theorem closure_union_eq_univ_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDense : Dense (A : Set X)) :
    closure (A ∪ B : Set X) = (Set.univ : Set X) := by
  classical
  -- From density we know `closure A = univ`.
  have hClA : closure (A : Set X) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).1 hDense
  -- Compute the closure of the union using distributivity over `closure`.
  calc
    closure (A ∪ B : Set X)
        = closure (A : Set X) ∪ closure (B : Set X) := by
          simpa [closure_union]
    _ = (Set.univ : Set X) ∪ closure (B : Set X) := by
          simpa [hClA]
    _ = (Set.univ : Set X) := by
          simpa [Set.univ_union]