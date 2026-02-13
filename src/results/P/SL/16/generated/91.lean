

theorem Topology.P3_union_right_dense {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h_dense : closure B = (Set.univ : Set X)) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Use commutativity of `∪` to apply the existing `P3_union_left_dense`.
  have h : Topology.P3 (X := X) (B ∪ A) :=
    Topology.P3_union_left_dense (X := X) (A := B) (B := A) h_dense
  simpa [Set.union_comm] using h