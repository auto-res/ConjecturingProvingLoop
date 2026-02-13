

theorem interior_closure_interior_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior ((A ∩ B) : Set X)))
      ⊆ interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- First component: `x ∈ interior (closure (interior A))`.
  have hxA : x ∈ interior (closure (interior A)) := by
    -- Show the required set inclusion and apply `hx`.
    have hIncl :
        closure (interior ((A ∩ B) : Set X))
          ⊆ closure (interior A) := by
      apply closure_mono
      intro y hy
      -- From `y ∈ interior (A ∩ B)` deduce `y ∈ interior A`.
      have hPair := (interior_inter_subset (A := A) (B := B)) hy
      exact hPair.1
    exact (interior_mono hIncl) hx
  -- Second component: `x ∈ interior (closure (interior B))`.
  have hxB : x ∈ interior (closure (interior B)) := by
    -- Analogous argument with `B`.
    have hIncl :
        closure (interior ((A ∩ B) : Set X))
          ⊆ closure (interior B) := by
      apply closure_mono
      intro y hy
      have hPair := (interior_inter_subset (A := A) (B := B)) hy
      exact hPair.2
    exact (interior_mono hIncl) hx
  exact And.intro hxA hxB