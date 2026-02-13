

theorem P3_inter_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hA_P3 : Topology.P3 (A : Set X)) (hB_P3 : Topology.P3 (B : Set X)) :
    Topology.P3 (A ∩ B) := by
  -- From `P3` and closedness, both `A` and `B` are open.
  have hA_open : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P3 (A := A) hA_closed hA_P3
  have hB_open : IsOpen (B : Set X) :=
    isOpen_of_isClosed_and_P3 (A := B) hB_closed hB_P3
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B : Set X) := hA_open.inter hB_open
  -- Any open set satisfies `P3`.
  simpa using Topology.P3_of_isOpen (A := A ∩ B) hOpen