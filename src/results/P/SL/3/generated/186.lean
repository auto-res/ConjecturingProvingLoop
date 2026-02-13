

theorem closure_interior_subset_interior_closure_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) →
      closure (interior (A : Set X)) ⊆ interior (closure (A : Set X)) := by
  intro hP3
  -- Unfold the definition of `P3` for `closure A`.
  dsimp [Topology.P3] at hP3
  -- We show that every point of `closure (interior A)` lies in `interior (closure A)`.
  intro x hxInt
  -- First, `x` belongs to `closure A`, by monotonicity of `closure`.
  have hxCl : (x : X) ∈ closure (A : Set X) :=
    (closure_interior_subset_closure (A := A)) hxInt
  -- Apply `P3` for `closure A`.
  have hxIntCl :
      (x : X) ∈ interior (closure (closure (A : Set X))) :=
    hP3 hxCl
  -- Simplify the double closure.
  simpa [closure_closure] using hxIntCl