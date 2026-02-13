

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  -- First, `x` belongs to the closure of `A`.
  have hxClosure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  -- Since `closure A` is open, its interior is itself.
  have hxInterior : (x : X) ∈ interior (closure (A : Set X)) := by
    simpa [hOpen.interior_eq] using hxClosure
  exact hxInterior