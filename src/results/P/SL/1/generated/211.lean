

theorem Topology.P3_of_between
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure A)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  -- Step 1: upgrade `x ∈ B` to `x ∈ interior (closure A)`.
  have hxIntA : x ∈ interior (closure A) := hBsubset hxB
  -- Step 2: use monotonicity of `closure` and `interior` to reach `closure B`.
  have hclosure : closure A ⊆ closure B := closure_mono hAB
  have hIntMono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono hclosure
  exact hIntMono hxIntA