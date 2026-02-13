

theorem Topology.P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed A → IsClosed B → Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hA_closed hB_closed hA_P2 hB_P2
  -- From `P2` and closedness we obtain that `A` and `B` are open.
  have hA_open : IsOpen A :=
    (Topology.isOpen_of_P2_of_isClosed (A := A) hA_closed hA_P2)
  have hB_open : IsOpen B :=
    (Topology.isOpen_of_P2_of_isClosed (A := B) hB_closed hB_P2)
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA_open.inter hB_open
  -- An open set always satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A ∩ B) hOpen