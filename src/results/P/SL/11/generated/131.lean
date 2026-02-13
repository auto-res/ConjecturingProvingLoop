

theorem P2_of_P1_and_open_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpen : IsOpen (closure (interior A))) :
    Topology.P2 A := by
  dsimp [Topology.P2]   -- we need to show `A ⊆ interior (closure (interior A))`
  intro x hxA
  -- From `P1`, obtain membership in the closure of the interior.
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  -- Since `closure (interior A)` is open, its interior is itself.
  have hIntEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Conclude the desired membership using the equality.
  simpa [hIntEq] using hxCl