

theorem Topology.P1_union_right_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior B) = (Set.univ : Set X)) :
    Topology.P1 (X := X) (A ∪ B) := by
  have h : Topology.P1 (X := X) (B ∪ A) :=
    Topology.P1_union_left_denseInterior (X := X) (A := B) (B := A) h_dense
  simpa [Set.union_comm] using h