

theorem P3_of_subset_and_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure A)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  -- From `hxB : x ∈ B` and `hBsubset`, we obtain `x ∈ interior (closure A)`.
  have hxIntClA : x ∈ interior (closure A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have hClSub : closure A ⊆ closure B := closure_mono hAB
  -- Taking interiors preserves inclusions.
  have hIntSub : interior (closure A) ⊆ interior (closure B) :=
    interior_mono hClSub
  -- Combine the two facts to place `x` in `interior (closure B)`.
  exact hIntSub hxIntClA