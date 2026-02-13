

theorem Topology.P2_of_P1_open_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpen : IsOpen (closure (interior A))) :
    Topology.P2 A := by
  dsimp [Topology.P2] at *
  intro x hxA
  -- From `P1` we have `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Because `closure (interior A)` is open, its interior is itself.
  have hEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Rewrite and conclude.
  simpa [hEq] using hx_cl