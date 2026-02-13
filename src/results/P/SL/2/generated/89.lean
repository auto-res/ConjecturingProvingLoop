

theorem Topology.P2_of_P1_and_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → IsOpen (closure (A : Set X)) → Topology.P2 A := by
  intro hP1 hOpenCl
  have hP3 : Topology.P3 A := Topology.isOpen_closure_implies_P3 (A := A) hOpenCl
  exact (Topology.P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩