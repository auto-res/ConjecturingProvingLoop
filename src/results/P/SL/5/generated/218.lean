

theorem interior_union_closure_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hIntA =>
      -- First case: `x ∈ interior A`.
      -- Upgrade to `x ∈ interior (closure A)`.
      have hIntClA : x ∈ interior (closure A) :=
        (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hIntA
      -- `closure A ⊆ closure (A ∪ B)`.
      have hsubset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      -- Hence the desired membership follows by monotonicity of `interior`.
      exact (interior_mono hsubset) hIntClA
  | inr hIntClB =>
      -- Second case: `x ∈ interior (closure B)`.
      -- `closure B ⊆ closure (A ∪ B)`.
      have hsubset : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      -- Conclude using monotonicity of `interior`.
      exact (interior_mono hsubset) hIntClB