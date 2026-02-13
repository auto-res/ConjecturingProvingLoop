

theorem P2_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hP2A ⊢
  intro x hx
  -- First locate `x` inside `interior (closure (interior A))`.
  have hxIntA : x ∈ interior (closure (interior A)) := by
    cases hx with
    | inl hxA => exact hP2A hxA
    | inr hxB => exact hBsubset hxB
  -- Monotonicity of `interior` and `closure` gives the required inclusion.
  have hMono :
      interior (closure (interior A)) ⊆
        interior (closure (interior (A ∪ B))) := by
    -- Step 1: `interior A ⊆ interior (A ∪ B)`.
    have hIntSub : interior A ⊆ interior (A ∪ B) := by
      have hSub : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
      exact interior_mono hSub
    -- Step 2: take closures.
    have hClosSub :
        closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono hIntSub
    -- Step 3: take interiors once more.
    exact interior_mono hClosSub
  exact hMono hxIntA