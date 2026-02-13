

theorem open_union_three_has_all_Ps {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    Topology.P1 (A ∪ B ∪ C) ∧ Topology.P2 (A ∪ B ∪ C) ∧ Topology.P3 (A ∪ B ∪ C) := by
  -- The triple union of open sets is open.
  have hOpen : IsOpen ((A ∪ B ∪ C) : Set X) :=
    isOpen_union_three hA hB hC
  -- Every open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_has_all_Ps
      (X := X) (A := ((A ∪ B ∪ C) : Set X)) hOpen