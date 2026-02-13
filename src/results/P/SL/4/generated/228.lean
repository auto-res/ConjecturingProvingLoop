

theorem P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h1 : Topology.P2 (closure A) ↔ Topology.P3 (closure A) :=
    Topology.P2_iff_P3_closure (A := A)
  have h2 : Topology.P3 (closure A) ↔ IsOpen (closure A) :=
    Topology.P3_closure_iff_isOpen_closure (A := A)
  exact h1.trans h2