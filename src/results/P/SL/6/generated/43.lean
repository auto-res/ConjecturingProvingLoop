

theorem P1_and_open_closure_interior_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X))
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (A : Set X) := by
  dsimp [Topology.P2] at *
  intro x hx
  -- From `P1`, we obtain membership in `closure (interior A)`.
  have hx' : x ∈ closure (interior A) := hP1 hx
  -- Since this set is open, its interior equals itself.
  have hInt : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Rewriting with this equality gives the desired result.
  simpa [hInt] using hx'