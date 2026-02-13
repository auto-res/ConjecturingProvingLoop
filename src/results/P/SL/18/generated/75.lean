

theorem P2_closure_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure (A : Set X)) := by
  have h : Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) :=
    Topology.P2_closure_iff_open_closure (A := A)
  exact (h.mpr hOpen)