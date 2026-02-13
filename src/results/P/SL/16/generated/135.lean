

theorem Topology.P2_union_right_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior B) = (Set.univ : Set X)) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- Apply the existing left-dense lemma after swapping `A` and `B`.
  have h : Topology.P2 (X := X) (B ∪ A) :=
    Topology.P2_union_left_denseInterior (X := X) (A := B) (B := A) h_dense
  simpa [Set.union_comm] using h