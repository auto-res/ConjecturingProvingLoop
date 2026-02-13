

theorem P1_union_P2 {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P2 B → P1 (A ∪ B) := by
  intro hP1 hP2
  -- unfold the definitions of the predicates
  unfold P1 at hP1 ⊢
  unfold P2 at hP2
  intro x hx
  cases hx with
  | inl hxA =>
      -- case `x ∈ A`
      have hx_cl : x ∈ closure (interior A) := hP1 hxA
      have h_subset :
          (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono Set.subset_union_left)
      exact h_subset hx_cl
  | inr hxB =>
      -- case `x ∈ B`
      have hx_int : x ∈ interior (closure (interior B)) := hP2 hxB
      have hx_cl : x ∈ closure (interior B) := interior_subset hx_int
      have h_subset :
          (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono Set.subset_union_right)
      exact h_subset hx_cl