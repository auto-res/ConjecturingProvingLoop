

theorem Topology.P3_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed A → IsClosed B → Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hClosedA hClosedB hP3A hP3B
  -- From closedness and `P3`, we infer that both `A` and `B` are open.
  have hOpenA : IsOpen A :=
    Topology.isClosed_P3_implies_isOpen (A := A) hClosedA hP3A
  have hOpenB : IsOpen B :=
    Topology.isClosed_P3_implies_isOpen (A := B) hClosedB hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (A := A ∩ B) hOpenInter