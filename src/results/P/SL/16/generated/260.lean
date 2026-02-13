

theorem Topology.closure_interior_inter_closure_subset_inter_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ closure B)) ⊆
      closure (interior A) ∩ closure (interior (closure B)) := by
  intro x hx
  -- `interior (A ∩ closure B)` is contained in `interior A`
  have h_left : interior (A ∩ closure B) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ closure B : Set X) ⊆ A)
  -- Hence `x ∈ closure (interior A)`
  have hx_left : x ∈ closure (interior A) :=
    (closure_mono h_left) hx
  -- Similarly, `interior (A ∩ closure B)` is contained in `interior (closure B)`
  have h_right : interior (A ∩ closure B) ⊆ interior (closure B) := by
    have h_sub : (A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact interior_mono h_sub
  -- Thus `x ∈ closure (interior (closure B))`
  have hx_right : x ∈ closure (interior (closure B)) :=
    (closure_mono h_right) hx
  exact And.intro hx_left hx_right