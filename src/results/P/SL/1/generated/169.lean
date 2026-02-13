

theorem Topology.interior_closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Membership in `interior (closure A)`
  have hA : closure (A ∩ interior B) ⊆ closure A := by
    apply closure_mono
    intro y hy
    exact hy.1
  have hxA : x ∈ interior (closure A) := (interior_mono hA) hx
  -- Membership in `interior (closure B)`
  have hB : closure (A ∩ interior B) ⊆ closure B := by
    -- Since `interior B ⊆ B`, the desired inclusion follows.
    have hsub : (A ∩ interior B : Set X) ⊆ B := by
      intro y hy
      exact (interior_subset : interior B ⊆ B) hy.2
    exact closure_mono hsub
  have hxB : x ∈ interior (closure B) := (interior_mono hB) hx
  exact And.intro hxA hxB