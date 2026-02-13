

theorem Topology.P2_of_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B)
    (hB : B ⊆ interior (closure (interior A))) :
    Topology.P2 (X := X) B := by
  dsimp [Topology.P2] at *
  intro x hxB
  -- From the hypothesis `hB`, `x` lies in `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := hB hxB
  -- We show that this set is contained in `interior (closure (interior B))`.
  have h_incl :
      interior (closure (interior A)) ⊆
        interior (closure (interior B)) := by
    -- Step 1: `interior A ⊆ interior B` since `A ⊆ B`.
    have h₁ : (interior A : Set X) ⊆ interior B :=
      interior_mono hAB
    -- Step 2: take closures.
    have h₂ : closure (interior A : Set X) ⊆ closure (interior B) :=
      closure_mono h₁
    -- Step 3: take interiors once more.
    exact interior_mono h₂
  -- Conclude that `x ∈ interior (closure (interior B))`.
  exact h_incl hx₁