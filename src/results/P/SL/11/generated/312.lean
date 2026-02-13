

theorem P3_of_P1_and_open_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A)
    (hOpen : IsOpen (closure (interior A))) :
    Topology.P3 A := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- Step 1: `P1` sends `x` into `closure (interior A)`.
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  -- Step 2: since `closure (interior A)` is open, its interior is itself.
  have hIntEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Reinterpret membership using the interior.
  have hxInt : x ∈ interior (closure (interior A)) := by
    simpa [hIntEq] using hxCl
  -- Step 3: monotonicity of `interior` gives the desired containment.
  have hsubset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_closure_interior_subset (A := A)
  exact hsubset hxInt