

theorem Topology.P2_P3_closure_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P2 (closure (A : Set X)) ∧ Topology.P3 (closure (A : Set X))) ↔
      IsOpen (closure (A : Set X)) := by
  have hP2 := (Topology.P2_closure_iff_isOpen (A := A))
  have hP3 := (Topology.P3_closure_iff_isOpen (A := A))
  constructor
  · intro h
    exact (hP2).1 h.1
  · intro hOpen
    exact ⟨(hP2).2 hOpen, (hP3).2 hOpen⟩