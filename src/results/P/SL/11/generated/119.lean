

theorem P123_closure_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpenCl : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure A) :=
    Topology.P1_of_open_closure (A := A) hOpenCl
  have hP2 : Topology.P2 (closure A) :=
    Topology.P2_of_open_closure (A := A) hOpenCl
  have hP3 : Topology.P3 (closure A) :=
    (Topology.P3_closure_iff_open (A := A)).mpr hOpenCl
  exact ⟨hP1, hP2, hP3⟩