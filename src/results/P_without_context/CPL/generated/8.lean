

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  have : (x : X) ∈ interior (Set.univ : Set X) := by
    simpa [interior_univ] using hx
  exact subset_closure this

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2 x hx
  exact (interior_mono (closure_mono interior_subset)) (hP2 hx)

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure A)) := by
  intro x hx
  -- First, `interior (closure A)` is contained in the closure of itself
  have hcl : (interior (closure A)) ⊆ closure (interior (closure A)) := by
    intro y hy
    exact subset_closure hy
  -- Take interiors of both sides of this inclusion
  have hsub :
      interior (closure A) ⊆
        interior (closure (interior (closure A))) := by
    -- `interior_mono` gives the inclusion between interiors
    -- The left‐hand side simplifies with `interior_interior`
    have : interior (interior (closure A)) ⊆
        interior (closure (interior (closure A))) :=
      interior_mono hcl
    simpa [interior_interior] using this
  -- Apply the inclusion to the given point and rewrite the goal
  have : x ∈ interior (closure (interior (closure A))) := hsub hx
  simpa [interior_interior] using this

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB x hx
  cases hx with
  | inl hxA =>
      have : x ∈ interior (closure (A ∪ B)) :=
        (interior_mono
          (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)))
          (hA hxA)
      exact this
  | inr hxB =>
      have : x ∈ interior (closure (A ∪ B)) :=
        (interior_mono
          (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)))
          (hB hxB)
      exact this