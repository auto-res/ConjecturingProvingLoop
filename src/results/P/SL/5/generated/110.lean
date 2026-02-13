

theorem interior_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Step 1: `x ∈ interior (closure A)`
      have hxA' : x ∈ interior (closure A) :=
        (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxA
      -- Step 2: `closure A ⊆ closure (A ∪ B)`
      have hsubset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Step 3: `interior (closure A) ⊆ interior (closure (A ∪ B))`
      have hsubset_int :
          interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset
      exact hsubset_int hxA'
  | inr hxB =>
      -- Symmetric argument for `B`
      have hxB' : x ∈ interior (closure B) :=
        (interior_mono (subset_closure : (B : Set X) ⊆ closure B)) hxB
      have hsubset : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      have hsubset_int :
          interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset
      exact hsubset_int hxB'