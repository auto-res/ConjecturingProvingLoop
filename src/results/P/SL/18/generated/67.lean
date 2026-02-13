

theorem P2_of_P1_and_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpen : IsOpen (closure (interior A))) :
    Topology.P2 A := by
  dsimp [Topology.P2, Topology.P1] at *
  intro x hxA
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  have hIntEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  simpa [hIntEq] using hxCl