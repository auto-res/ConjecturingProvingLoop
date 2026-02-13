

theorem P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [hOpen.interior_eq] using hx_cl