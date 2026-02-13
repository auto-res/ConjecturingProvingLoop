

theorem empty_has_all_Ps {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  have hOpen : IsOpen (∅ : Set X) := isOpen_empty
  exact Topology.isOpen_has_all_Ps (X := X) (A := (∅ : Set X)) hOpen