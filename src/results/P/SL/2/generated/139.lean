

theorem Topology.P2_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (A : Set X) → IsClosed (B : Set X) →
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hClosedA hClosedB hP2A hP2B
  -- From closedness and `P2`, we infer that both `A` and `B` are open.
  have hOpenA : IsOpen (A : Set X) :=
    Topology.isClosed_P2_implies_isOpen (A := A) hClosedA hP2A
  have hOpenB : IsOpen (B : Set X) :=
    Topology.isClosed_P2_implies_isOpen (A := B) hClosedB hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen ((A ∩ B) : Set X) := hOpenA.inter hOpenB
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (A := A ∩ B) hOpenInter