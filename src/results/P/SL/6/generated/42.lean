

theorem P1_and_open_closure_interior_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (A : Set X))
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  -- From `P1`, we have membership in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hx
  -- Since this set is open, its interior equals itself.
  have hEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Reinterpret the membership using this equality.
  have hx_int : x ∈ interior (closure (interior A)) := by
    simpa [hEq] using hx_cl
  -- Monotonicity of `interior` and `closure` gives the desired inclusion.
  have hIncl : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hIncl hx_int