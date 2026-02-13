

theorem Topology.P3_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed A → IsClosed B → Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hA_closed hB_closed hA_P3 hB_P3
  -- From `P3` and closedness we obtain that `A` and `B` are open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hA_P3
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (A := B) hB_closed).1 hB_P3
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA_open.inter hB_open
  -- An open set always satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A ∩ B) hOpen