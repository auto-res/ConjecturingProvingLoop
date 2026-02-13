

theorem Topology.interior_closure_union_three_subset {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure B) ∪ interior (closure C) ⊆
      interior (closure (A ∪ B ∪ C : Set X)) := by
  -- First, deal with the union of `A` and `B`.
  have hAB :
      interior (closure (A : Set X)) ∪ interior (closure B) ⊆
        interior (closure (A ∪ B : Set X)) :=
    Topology.interior_closure_union_subset (X := X) (A := A) (B := B)
  -- Next, add `C` to the picture.
  have hABC :
      interior (closure (A ∪ B : Set X)) ∪ interior (closure C) ⊆
        interior (closure ((A ∪ B) ∪ C : Set X)) :=
    Topology.interior_closure_union_subset (X := X) (A := A ∪ B) (B := C)
  -- Rewrite `((A ∪ B) ∪ C)` using associativity.
  have hABC' :
      interior (closure (A ∪ B : Set X)) ∪ interior (closure C) ⊆
        interior (closure (A ∪ B ∪ C : Set X)) := by
    simpa [Set.union_assoc] using hABC
  -- Now prove the desired inclusion.
  intro x hx
  -- Analyse the membership of `x` in the triple union.
  cases hx with
  | inl hx_left =>
      -- `x` lies in the first two terms of the triple union.
      have hxAB : x ∈ interior (closure (A ∪ B : Set X)) := hAB hx_left
      have hxABC : x ∈
          interior (closure (A ∪ B : Set X)) ∪ interior (closure C) :=
        Or.inl hxAB
      exact hABC' hxABC
  | inr hxC =>
      -- `x` lies in the third term `interior (closure C)`.
      have hxABC : x ∈
          interior (closure (A ∪ B : Set X)) ∪ interior (closure C) :=
        Or.inr hxC
      exact hABC' hxABC