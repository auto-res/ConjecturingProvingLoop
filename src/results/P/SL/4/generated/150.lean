

theorem interior_closure_inter_interior_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure (A ∩ interior B)` is contained in `closure A`
  have hA : closure (A ∩ interior B) ⊆ closure A :=
    closure_mono Set.inter_subset_left
  -- `closure (A ∩ interior B)` is contained in `closure B`
  have hB : closure (A ∩ interior B) ⊆ closure B := by
    -- First, note that `A ∩ interior B ⊆ B`
    have h : A ∩ interior B ⊆ B := by
      intro y hy
      exact interior_subset hy.2
    -- Taking closures preserves the inclusion
    exact closure_mono h
  -- Taking interiors preserves these inclusions
  have hA_int : interior (closure (A ∩ interior B)) ⊆ interior (closure A) :=
    interior_mono hA
  have hB_int : interior (closure (A ∩ interior B)) ⊆ interior (closure B) :=
    interior_mono hB
  -- Apply the inclusions to the given point `x`
  have hxA : x ∈ interior (closure A) := hA_int hx
  have hxB : x ∈ interior (closure B) := hB_int hx
  exact And.intro hxA hxB