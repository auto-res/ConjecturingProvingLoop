

theorem Topology.frontier_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier ((A ∪ B) : Set X) ⊆ frontier (A : Set X) ∪ frontier (B : Set X) := by
  intro x hx
  rcases hx with ⟨hx_closureUnion, hx_not_intUnion⟩
  -- `x` is in the closure of `A` or of `B` (since `closure (A ∪ B) = closure A ∪ closure B`)
  have hClosure : x ∈ closure (A : Set X) ∨ x ∈ closure (B : Set X) := by
    have h : x ∈ closure (A : Set X) ∪ closure (B : Set X) := by
      simpa [closure_union] using hx_closureUnion
    simpa [Set.mem_union] using h
  -- Analyse the two cases.
  cases hClosure with
  | inl hx_closureA =>
      -- Case: `x ∈ closure A`
      by_cases hx_intA : x ∈ interior (A : Set X)
      · -- If `x` were in `interior A`, it would be in `interior (A ∪ B)`, contradiction.
        have hsubset :
            interior (A : Set X) ∪ interior (B : Set X) ⊆
              interior ((A ∪ B) : Set X) :=
          interior_union (A := A) (B := B)
        have hx_intUnion : x ∈ interior ((A ∪ B) : Set X) :=
          hsubset (Or.inl hx_intA)
        have hFalse : False := hx_not_intUnion hx_intUnion
        exact False.elim hFalse
      · -- Otherwise, `x` is not in `interior A`; hence `x ∈ frontier A`.
        exact Or.inl (And.intro hx_closureA hx_intA)
  | inr hx_closureB =>
      -- Case: `x ∈ closure B`
      by_cases hx_intB : x ∈ interior (B : Set X)
      · -- If `x` were in `interior B`, it would be in `interior (A ∪ B)`, contradiction.
        have hsubset :
            interior (A : Set X) ∪ interior (B : Set X) ⊆
              interior ((A ∪ B) : Set X) :=
          interior_union (A := A) (B := B)
        have hx_intUnion : x ∈ interior ((A ∪ B) : Set X) :=
          hsubset (Or.inr hx_intB)
        have hFalse : False := hx_not_intUnion hx_intUnion
        exact False.elim hFalse
      · -- Otherwise, `x` is not in `interior B`; hence `x ∈ frontier B`.
        exact Or.inr (And.intro hx_closureB hx_intB)