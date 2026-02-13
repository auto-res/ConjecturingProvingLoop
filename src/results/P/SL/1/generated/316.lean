

theorem Topology.closure_interior_union_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∪ B)) ⊆ closure A ∪ closure B := by
  intro x hx
  -- Step 1: `interior (A ∪ B)` is contained in `A ∪ B`.
  have h₁ : interior (A ∪ B) ⊆ (A ∪ B : Set X) := interior_subset
  -- Step 2: Taking closures preserves the inclusion.
  have h₂ : closure (interior (A ∪ B)) ⊆ closure (A ∪ B) :=
    closure_mono h₁
  -- Step 3: Rewrite `closure (A ∪ B)` using `closure_union`.
  have hx' : x ∈ closure (A ∪ B) := h₂ hx
  simpa [closure_union] using hx'