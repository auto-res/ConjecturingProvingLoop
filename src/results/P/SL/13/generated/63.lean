

theorem Topology.isOpen_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    Topology.P3 (X:=X) A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have h_eq : interior (closure (A : Set X)) = closure (A : Set X) :=
    h_open.interior_eq
  simpa [h_eq] using hx_cl